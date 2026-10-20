//! Reachable-state-guided generalization.
//!
//! The ideas follow "Pushing to the Top" (Gurfinkel and Ivrii, FMCAD 2015):
//! IC3 learns lemmas that are inductive relative to low frames but are
//! violated by states that are reachable deeper down, and then spends effort
//! trying to push them. Concrete reachable states are a cheap certificate that
//! a lemma can never be part of an inductive invariant.
//!
//! This module provides
//! - [`ReachCache`]: a cache of concrete reachable states (over latch bits),
//!   bucketed per literal so that "does this cube contain a known reachable
//!   state?" costs a scan over the smallest bucket among the cube's literals;
//! - may-proof obligations: after a generalization that shrinks an obligation
//!   by more than one literal, the generalized cube is enqueued as a
//!   lower-priority "may" obligation at the frame its lemma could not be pushed
//!   to. May obligations never produce counterexamples. When one reaches the
//!   initial states, concrete states along its chain are computed with SAT
//!   successor queries and stored in the cache;
//! - the uses of the cache: rejecting MIC candidates that contain a known
//!   reachable state (and re-adding literals to cores that would), skipping
//!   push attempts that are known to fail, and closing may obligations.
//!
//! Every cached state is reached from an initial state by a chain of valid
//! transitions (constraints hold at every step), so it lies in every frame
//! `F_i` with `i >= depth`. The cache is only used to *avoid* work or to make
//! lemmas *stronger* (more literals), so it can never make IC3 unsound.

use super::{IC3, proofoblig::ProofObligation};
use crate::{gipsat::TransysSolver, transys::TransysIf};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarMap, satif::Satif};
use rand::RngExt;
use std::fmt::{self, Debug};

const NO_LATCH: u32 = u32::MAX;
/// Upper bound on `num_latch * capacity` (bucket entries) to keep memory bounded.
const BUCKET_ENTRY_BUDGET: usize = 1 << 25;
/// A may obligation is dropped after it has been retried this many times.
const MAY_ACT_LIMIT: f64 = 10.0;
/// Maximum number of queued may obligations.
const MAY_QUEUE_LIMIT: usize = 4096;
/// Maximum accumulated may credit (in obligations).
const MAY_CREDIT_LIMIT: f64 = 16.0;

struct CachedState {
    val: Vec<u64>,
    known: Vec<u64>,
    /// The state is reachable within `depth` steps from an initial state.
    depth: usize,
    /// Aged hit count (halved at each cleanup).
    hits: u32,
    total_hits: u64,
    last_use: u64,
}

impl CachedState {
    #[inline]
    fn value(&self, idx: usize) -> Option<bool> {
        let (w, b) = (idx / 64, idx % 64);
        (self.known[w] >> b & 1 == 1).then_some(self.val[w] >> b & 1 == 1)
    }
}

#[derive(Default, Clone)]
pub struct ReachCacheStat {
    pub lookups: u64,
    pub hits: u64,
    pub scanned: u64,
    pub inserts: u64,
    pub duplicates: u64,
    pub evictions: u64,
    pub cleanups: u64,
    pub max_size: usize,
}

/// Cache of concrete states known to be reachable from the initial states.
pub struct ReachCache {
    latch_idx: VarMap<u32>,
    num_latch: usize,
    num_word: usize,
    states: Vec<CachedState>,
    /// `bucket[2 * latch_idx + !polarity]` holds the states satisfying that literal.
    bucket: Vec<Vec<u32>>,
    capacity: usize,
    min_cap: usize,
    max_cap: usize,
    clock: u64,
    pub stat: ReachCacheStat,
}

impl ReachCache {
    pub fn new(latches: &[Var], min_cap: usize, max_cap: usize) -> Self {
        let mut latch_idx = VarMap::new();
        if let Some(m) = latches.iter().max() {
            latch_idx.reserve(*m);
        }
        for v in latch_idx.iter_mut() {
            *v = NO_LATCH;
        }
        for (i, l) in latches.iter().enumerate() {
            latch_idx[*l] = i as u32;
        }
        let num_latch = latches.len();
        let max_cap = max_cap.min(BUCKET_ENTRY_BUDGET / num_latch.max(1)).max(8);
        let min_cap = min_cap.min(max_cap).max(4);
        Self {
            latch_idx,
            num_latch,
            num_word: num_latch.div_ceil(64),
            states: Vec::new(),
            bucket: vec![Vec::new(); 2 * num_latch],
            capacity: min_cap,
            min_cap,
            max_cap,
            clock: 0,
            stat: Default::default(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.states.len()
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    fn idx(&self, var: Var) -> Option<usize> {
        let i = *self.latch_idx.get(Into::<usize>::into(var))?;
        (i != NO_LATCH).then_some(i as usize)
    }

    #[inline]
    fn bucket_of(&self, lit: Lit) -> Option<usize> {
        self.idx(lit.var())
            .map(|i| 2 * i + usize::from(!lit.polarity()))
    }

    #[inline]
    fn state_sat(&self, s: &CachedState, lit: Lit) -> bool {
        match self.idx(lit.var()) {
            Some(i) => s.value(i) == Some(lit.polarity()),
            None => false,
        }
    }

    /// Whether the cached state `id` definitely satisfies `lit`.
    #[inline]
    pub fn satisfies(&self, id: usize, lit: Lit) -> bool {
        self.state_sat(&self.states[id], lit)
    }

    #[inline]
    pub fn depth(&self, id: usize) -> usize {
        self.states[id].depth
    }

    /// The cached state `id` as a cube over the latches.
    pub fn state_lits(&self, id: usize, latches: &[Var]) -> LitVec {
        let s = &self.states[id];
        latches
            .iter()
            .filter_map(|l| {
                let i = self.idx(*l)?;
                s.value(i).map(|v| l.lit().not_if(!v))
            })
            .collect()
    }

    fn find_inner(&mut self, cube: &[Lit], max_depth: usize, count: bool) -> Option<usize> {
        if count {
            self.stat.lookups += 1;
        }
        if self.states.is_empty() {
            return None;
        }
        let mut best: Option<usize> = None;
        for l in cube.iter() {
            let b = self.bucket_of(*l)?;
            if best.is_none_or(|x| self.bucket[b].len() < self.bucket[x].len()) {
                best = Some(b);
                if self.bucket[b].is_empty() {
                    return None;
                }
            }
        }
        let ids: &[u32] = match best {
            Some(b) => &self.bucket[b],
            None => return None,
        };
        let mut found = None;
        let mut scanned = 0;
        for &id in ids.iter() {
            scanned += 1;
            let s = &self.states[id as usize];
            if s.depth <= max_depth && cube.iter().all(|l| self.state_sat(s, *l)) {
                found = Some(id as usize);
                break;
            }
        }
        if count {
            self.stat.scanned += scanned;
        }
        let id = found?;
        if count {
            self.clock += 1;
            self.stat.hits += 1;
            let s = &mut self.states[id];
            s.hits = s.hits.saturating_add(1);
            s.total_hits += 1;
            s.last_use = self.clock;
        }
        Some(id)
    }

    /// Returns a cached state of depth at most `max_depth` that lies in `cube`
    /// (satisfies every literal of it).
    #[inline]
    pub fn find(&mut self, cube: &[Lit], max_depth: usize) -> Option<usize> {
        self.find_inner(cube, max_depth, true)
    }

    /// Inserts a state (a cube over latches, normally total) reachable within
    /// `depth` steps. Returns whether the cache changed.
    pub fn insert(&mut self, state: &[Lit], depth: usize) -> bool {
        if state.is_empty() {
            return false;
        }
        if let Some(id) = self.find_inner(state, usize::MAX, false) {
            self.stat.duplicates += 1;
            let s = &mut self.states[id];
            s.depth = s.depth.min(depth);
            return false;
        }
        if self.states.len() >= self.capacity {
            self.cleanup();
        }
        let mut val = vec![0u64; self.num_word];
        let mut known = vec![0u64; self.num_word];
        for l in state.iter() {
            if let Some(i) = self.idx(l.var()) {
                known[i / 64] |= 1 << (i % 64);
                if l.polarity() {
                    val[i / 64] |= 1 << (i % 64);
                }
            }
        }
        let id = self.states.len() as u32;
        for l in state.iter() {
            if let Some(b) = self.bucket_of(*l) {
                self.bucket[b].push(id);
            }
        }
        self.clock += 1;
        self.states.push(CachedState {
            val,
            known,
            depth,
            hits: 0,
            total_hits: 0,
            last_use: self.clock,
        });
        self.stat.inserts += 1;
        self.stat.max_size = self.stat.max_size.max(self.states.len());
        true
    }

    /// Adapts the capacity to how useful the cache has been, evicts cold
    /// states and ages the hit counts.
    fn cleanup(&mut self) {
        self.stat.cleanups += 1;
        let useful = self.states.iter().filter(|s| s.hits > 0).count();
        if useful * 2 >= self.states.len() {
            self.capacity = (self.capacity * 2).min(self.max_cap);
        } else if useful * 8 < self.states.len() {
            self.capacity = (self.capacity / 2).max(self.min_cap);
        }
        let target = self.capacity * 3 / 4;
        if self.states.len() > target {
            // Keep hot and recently used states.
            self.states
                .sort_by(|a, b| b.hits.cmp(&a.hits).then(b.last_use.cmp(&a.last_use)));
            self.stat.evictions += (self.states.len() - target) as u64;
            self.states.truncate(target);
        }
        for s in self.states.iter_mut() {
            s.hits /= 2;
        }
        for b in self.bucket.iter_mut() {
            b.clear();
        }
        for (id, s) in self.states.iter().enumerate() {
            for i in 0..self.num_latch {
                if let Some(v) = s.value(i) {
                    self.bucket[2 * i + usize::from(!v)].push(id as u32);
                }
            }
        }
    }
}

#[derive(Default, Clone)]
pub struct ReachStat {
    /// MIC candidates rejected because they contain a cached state.
    pub mic_reject: u64,
    /// Literals re-added to cores to exclude cached states.
    pub core_refine: u64,
    /// Cores that contained a state of depth <= frame (must never happen).
    pub exact_violation: u64,
    /// Push attempts skipped because a cached state is known to block them.
    pub push_skip: u64,
    pub inf_push_skip: u64,
    pub may_created: u64,
    pub may_steps: u64,
    pub may_blocked: u64,
    pub may_preds: u64,
    pub may_reached_init: u64,
    pub may_closed_by_cache: u64,
    pub may_dropped: u64,
    pub may_lemma_inv: u64,
    pub witness_queries: u64,
    pub witness_fail: u64,
    pub witness_states: u64,
    pub sim_queries: u64,
    pub sim_states: u64,
}

pub struct Reach {
    pub cache: ReachCache,
    latches: Vec<Var>,
    /// `T` and constraints, no lemmas: used for successor queries.
    solver: Option<TransysSolver>,
    /// Like `solver`, with the initial-state constraints.
    init_solver: Option<TransysSolver>,
    /// Current and next latch variables (and inputs), the decision domain of
    /// the successor queries so that the successor state is total.
    domain: Vec<Var>,
    dead_roots: Vec<bool>,
    pub may_credit: f64,
    pub stat: ReachStat,
}

impl Reach {
    pub fn new(ic3: &IC3) -> Self {
        let latches = ic3.tsctx.latch.clone();
        let cache = ReachCache::new(&latches, ic3.cfg.reach_cap_min, ic3.cfg.reach_cap_max);
        let mut domain: Vec<Var> = latches.clone();
        domain.extend(latches.iter().map(|l| ic3.tsctx.next(l.lit()).var()));
        domain.extend(ic3.tsctx.input.iter().copied());
        domain.sort();
        domain.dedup();
        Self {
            cache,
            latches,
            solver: None,
            init_solver: None,
            domain,
            dead_roots: Vec::new(),
            may_credit: 0.0,
            stat: Default::default(),
        }
    }

    pub fn new_root(&mut self) -> u32 {
        self.dead_roots.push(false);
        (self.dead_roots.len() - 1) as u32
    }

    #[inline]
    pub fn root_dead(&self, root: u32) -> bool {
        self.dead_roots[root as usize]
    }

    fn prepare_solvers(&mut self, ic3: &IC3) {
        if self.solver.is_none() {
            self.solver = Some(TransysSolver::new(&ic3.tsctx));
            let mut init = TransysSolver::new(&ic3.tsctx);
            for c in ic3.tsctx.init.iter() {
                init.add_clause(c);
            }
            self.init_solver = Some(init);
        }
    }

    /// Solves `assump` on the (init) successor solver with a decision domain
    /// covering all current/next latches. Returns the (current, next) states.
    fn successor(&mut self, ic3: &IC3, init: bool, assump: &[Lit]) -> Option<(LitVec, LitVec)> {
        let slv = if init {
            self.init_solver.as_mut().unwrap()
        } else {
            self.solver.as_mut().unwrap()
        };
        if !slv
            .dcs
            .solve_with_domain(assump, self.domain.iter().copied())
        {
            return None;
        }
        let mut cur = LitVec::new();
        let mut nxt = LitVec::new();
        for l in self.latches.iter() {
            let lit = l.lit();
            if let Some(v) = slv.sat_value(lit) {
                cur.push(lit.not_if(!v));
            }
            if let Some(v) = slv.sat_value(ic3.tsctx.next(lit)) {
                nxt.push(lit.not_if(!v));
            }
        }
        Some((cur, nxt))
    }

    fn insert(&mut self, state: &LitVec, depth: usize) {
        if depth > 0 && self.cache.insert(state, depth) {
            self.stat.witness_states += 1;
        }
    }

    /// Computes concrete reachable states along `chain`. `chain[0]` contains
    /// either `start` (a cached reachable state of depth `start_depth`) or,
    /// if `start` is `None`, an initial state. Every consecutive pair of cubes
    /// is connected by a transition from every state of the first (as
    /// guaranteed by predecessor lifting), so successor queries succeed.
    fn witness(&mut self, ic3: &IC3, chain: &[LitOrdVec], start: Option<(LitVec, usize)>) {
        self.prepare_solvers(ic3);
        let (mut cur, mut depth, mut k) = match start {
            Some((s, d)) => (s, d, 1),
            None => {
                let mut assump: LitVec = chain[0].as_litvec().clone();
                if chain.len() > 1 {
                    assump.extend(ic3.tsctx.lits_next(chain[1].iter()));
                }
                self.stat.witness_queries += 1;
                let Some((s0, s1)) = self.successor(ic3, true, &assump) else {
                    self.stat.witness_fail += 1;
                    return;
                };
                if chain.len() > 1 {
                    self.insert(&s1, 1);
                    (s1, 1, 2)
                } else {
                    (s0, 0, 1)
                }
            }
        };
        while k < chain.len() {
            let mut assump = cur.clone();
            assump.extend(ic3.tsctx.lits_next(chain[k].iter()));
            self.stat.witness_queries += 1;
            let Some((_, next)) = self.successor(ic3, false, &assump) else {
                self.stat.witness_fail += 1;
                return;
            };
            cur = next;
            depth += 1;
            self.insert(&cur, depth);
            k += 1;
        }
    }

    /// Random walks from the initial states, seeding the cache with
    /// `steps` states.
    fn simulate(&mut self, ic3: &mut IC3, steps: usize) {
        const WALK_LEN: usize = 32;
        self.prepare_solvers(ic3);
        let mut done = 0;
        let mut fails = 0;
        while done < steps && fails < 16 {
            let rnd = |ic3: &mut IC3, vars: &mut dyn Iterator<Item = Var>| -> LitVec {
                vars.map(|v| v.lit().not_if(ic3.rng.random_bool(0.5)))
                    .collect()
            };
            let free_latches: Vec<Var> = self
                .latches
                .iter()
                .filter(|l| ic3.tsctx.init_map[**l].is_none())
                .copied()
                .collect();
            let inputs = ic3.tsctx.input.clone();
            let mut assump = rnd(ic3, &mut free_latches.iter().copied());
            assump.extend(rnd(ic3, &mut inputs.iter().copied()));
            self.stat.sim_queries += 1;
            let first = self
                .successor(ic3, true, &assump)
                .or_else(|| self.successor(ic3, true, &[]));
            let Some((_, mut cur)) = first else {
                fails += 1;
                continue;
            };
            let mut depth = 1;
            loop {
                if self.cache.insert(&cur, depth) {
                    self.stat.sim_states += 1;
                }
                done += 1;
                if depth >= WALK_LEN || done >= steps {
                    break;
                }
                let mut assump = cur.clone();
                assump.extend(rnd(ic3, &mut inputs.iter().copied()));
                self.stat.sim_queries += 1;
                let next = self
                    .successor(ic3, false, &assump)
                    .or_else(|| self.successor(ic3, false, &cur));
                let Some((_, next)) = next else {
                    fails += 1;
                    break;
                };
                cur = next;
                depth += 1;
            }
        }
    }
}

impl Debug for Reach {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = &self.cache.stat;
        let s = &self.stat;
        f.debug_struct("Reach")
            .field("cache_size", &self.cache.len())
            .field("cache_capacity", &self.cache.capacity())
            .field("cache_max_size", &c.max_size)
            .field("cache_lookups", &c.lookups)
            .field("cache_hits", &c.hits)
            .field("cache_scanned", &c.scanned)
            .field("cache_inserts", &c.inserts)
            .field("cache_duplicates", &c.duplicates)
            .field("cache_evictions", &c.evictions)
            .field("cache_cleanups", &c.cleanups)
            .field("mic_reject", &s.mic_reject)
            .field("core_refine", &s.core_refine)
            .field("exact_violation", &s.exact_violation)
            .field("push_skip", &s.push_skip)
            .field("inf_push_skip", &s.inf_push_skip)
            .field("may_created", &s.may_created)
            .field("may_steps", &s.may_steps)
            .field("may_blocked", &s.may_blocked)
            .field("may_preds", &s.may_preds)
            .field("may_reached_init", &s.may_reached_init)
            .field("may_closed_by_cache", &s.may_closed_by_cache)
            .field("may_dropped", &s.may_dropped)
            .field("may_lemma_inv", &s.may_lemma_inv)
            .field("witness_queries", &s.witness_queries)
            .field("witness_fail", &s.witness_fail)
            .field("witness_states", &s.witness_states)
            .field("sim_queries", &s.sim_queries)
            .field("sim_states", &s.sim_states)
            .finish()
    }
}

impl IC3 {
    /// Called once the frame-0 solver exists.
    pub(super) fn reach_init(&mut self) {
        if !self.cfg.reach_enabled() || self.reach.is_some() {
            return;
        }
        let mut reach = Reach::new(self);
        if self.cfg.reach_sim > 0 {
            reach.simulate(self, self.cfg.reach_sim);
        }
        self.reach = Some(reach);
    }

    #[inline]
    fn reach_mic_depth(&self, frame: usize) -> usize {
        if self.cfg.reach_mic_exact {
            frame
        } else {
            usize::MAX
        }
    }

    /// Whether the MIC candidate `cube` (a lemma for frame `frame`) should be
    /// rejected because it contains a known reachable state.
    pub(super) fn reach_mic_reject(&mut self, frame: usize, cube: &[Lit]) -> bool {
        if !self.cfg.reach_mic {
            return false;
        }
        let depth = self.reach_mic_depth(frame);
        let Some(reach) = self.reach.as_mut() else {
            return false;
        };
        if reach.cache.find(cube, depth).is_some() {
            reach.stat.mic_reject += 1;
            true
        } else {
            false
        }
    }

    /// `core` is the inductive core of the relatively inductive cube `cube`
    /// at `frame`; every cube between `core` and `cube` is relatively
    /// inductive as well. Re-adds literals of `cube` to `core` until it
    /// contains no known reachable state (if `cube` itself contains none).
    pub(super) fn reach_refine_core(
        &mut self,
        frame: usize,
        mut core: LitVec,
        cube: &[Lit],
    ) -> LitVec {
        if !self.cfg.reach_mic {
            return core;
        }
        let depth = self.reach_mic_depth(frame);
        let Some(reach) = self.reach.as_mut() else {
            return core;
        };
        while let Some(id) = reach.cache.find(&core, depth) {
            if reach.cache.depth(id) <= frame {
                reach.stat.exact_violation += 1;
            }
            let Some(l) = cube
                .iter()
                .find(|l| !core.contains(l) && !reach.cache.satisfies(id, **l))
            else {
                break;
            };
            core.push(*l);
            reach.stat.core_refine += 1;
        }
        core
    }

    /// Whether pushing the lemma `cube` into frame `frame` is known to fail:
    /// a state reachable within `frame` steps lies in the cube.
    pub(super) fn reach_push_blocked(&mut self, frame: usize, cube: &[Lit]) -> bool {
        if !self.cfg.reach_push {
            return false;
        }
        let Some(reach) = self.reach.as_mut() else {
            return false;
        };
        if reach.cache.find(cube, frame).is_some() {
            reach.stat.push_skip += 1;
            true
        } else {
            false
        }
    }

    /// Whether the lemma `cube` is known not to be part of any inductive invariant.
    pub(super) fn reach_inf_push_blocked(&mut self, cube: &[Lit]) -> bool {
        if !self.cfg.reach_push {
            return false;
        }
        let Some(reach) = self.reach.as_mut() else {
            return false;
        };
        if reach.cache.find(cube, usize::MAX).is_some() {
            reach.stat.inf_push_skip += 1;
            true
        } else {
            false
        }
    }

    /// Called after an ordinary obligation of `po_len` literals was
    /// generalized to `mic` whose lemma could not be pushed into `frame`.
    pub(super) fn may_create(&mut self, po_len: usize, frame: usize, mic: &LitVec) {
        if !self.cfg.may_po
            || frame > self.level()
            || po_len < mic.len() + self.cfg.may_po_min_shrink
        {
            return;
        }
        let Some(reach) = self.reach.as_mut() else {
            return;
        };
        if reach.cache.find(mic, usize::MAX).is_some() {
            return;
        }
        let root = reach.new_root();
        reach.stat.may_created += 1;
        let mut po = ProofObligation::new(frame, LitOrdVec::new(mic.clone()), vec![], 0, None);
        po.may_root = Some(root);
        self.add_may(po);
    }

    fn add_may(&mut self, po: ProofObligation) {
        self.may_obligations.add_if_absent(po);
        while self.may_obligations.len() > MAY_QUEUE_LIMIT {
            self.may_obligations.pop_lowest();
            self.reach.as_mut().unwrap().stat.may_dropped += 1;
        }
    }

    /// Accounts one ordinary obligation towards the may budget.
    #[inline]
    pub(super) fn may_earn(&mut self) {
        if self.cfg.may_po
            && let Some(reach) = self.reach.as_mut()
        {
            reach.may_credit = (reach.may_credit + self.cfg.may_po_share).min(MAY_CREDIT_LIMIT);
        }
    }

    /// Whether a may obligation should be processed now.
    #[inline]
    pub(super) fn may_turn(&self) -> bool {
        self.cfg.may_po
            && self.may_obligations.ready(self.level())
            && self.reach.as_ref().is_some_and(|r| r.may_credit >= 1.0)
    }

    /// Processes one may obligation. Returns true if an invariant was found.
    pub(super) fn may_step(&mut self) -> bool {
        let level = self.level();
        let reach = self.reach.as_mut().unwrap();
        reach.may_credit -= 1.0;
        let Some(mut po) = self.may_obligations.pop(level) else {
            reach.may_credit = reach.may_credit.min(0.0);
            return false;
        };
        let root = po.may_root.unwrap();
        if reach.root_dead(root) {
            return false;
        }
        reach.stat.may_steps += 1;
        if self.tsctx.cube_subsume_init(&po.state) {
            reach.stat.may_reached_init += 1;
            self.may_reached(&po, None);
            return false;
        }
        if po.frame == 0 {
            return false;
        }
        if let Some(id) = reach.cache.find(&po.state, usize::MAX) {
            reach.stat.may_closed_by_cache += 1;
            let start = (
                reach.cache.state_lits(id, &reach.latches),
                reach.cache.depth(id),
            );
            self.may_reached(&po, Some(start));
            return false;
        }
        if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.state) {
            if let Some(bf) = bf {
                po.push_to(bf + 1);
                self.add_may(po);
            }
            return false;
        }
        po.bump_act();
        if po.act > MAY_ACT_LIMIT {
            self.reach.as_mut().unwrap().stat.may_dropped += 1;
            return false;
        }
        if self
            .blocked(po.frame, &po.state)
            .with_act_order(false)
            .check()
        {
            self.reach.as_mut().unwrap().stat.may_blocked += 1;
            let Some(core) = self.solvers[po.frame - 1].inductive_core() else {
                let lemma = po.state.as_litvec().clone();
                let frame = po.frame;
                po.push_to(frame + 1);
                self.add_may(po);
                return self.add_lemma(frame, lemma, false, None);
            };
            let core = self.reach_refine_core(po.frame, core, po.state.as_litvec());
            let mic = self.mic(
                po.frame,
                core,
                &[],
                super::mic::MicType::from_config(&self.cfg),
            );
            let (frame, mic) = self.push_lemma(po.frame, mic);
            po.push_to(frame);
            self.add_may(po);
            if self.add_lemma(frame - 1, mic, false, None) {
                self.reach.as_mut().unwrap().stat.may_lemma_inv += 1;
                return true;
            }
        } else {
            let (model, inputs) = self.get_pred(po.frame, true);
            let mut pred = ProofObligation::new(
                po.frame - 1,
                LitOrdVec::new(model),
                inputs,
                po.depth + 1,
                Some(po.clone()),
            );
            pred.may_root = Some(root);
            self.reach.as_mut().unwrap().stat.may_preds += 1;
            self.add_may(pred);
            self.add_may(po);
        }
        false
    }

    /// The may obligation `po` contains a reachable state (an initial state,
    /// or the cached state `start`): computes concrete states along its chain
    /// and retires its root.
    fn may_reached(&mut self, po: &ProofObligation, start: Option<(LitVec, usize)>) {
        let mut chain = vec![po.state.clone()];
        let mut n = po.next.clone();
        while let Some(p) = n {
            chain.push(p.state.clone());
            n = p.next.clone();
        }
        let mut reach = self.reach.take().unwrap();
        reach.dead_roots[po.may_root.unwrap() as usize] = true;
        reach.witness(self, &chain, start);
        self.reach = Some(reach);
    }

    pub(super) fn reach_statistic(&self) -> Option<String> {
        self.reach.as_ref().map(|r| format!("{r:#?}"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lits(v: &[i32]) -> LitVec {
        v.iter().map(|x| Lit::from(*x)).collect()
    }

    fn cache() -> ReachCache {
        let latches: Vec<Var> = (1..=6).map(Var::new).collect();
        ReachCache::new(&latches, 4, 64)
    }

    #[test]
    fn find_respects_cube_and_depth() {
        let mut c = cache();
        assert!(c.insert(&lits(&[1, -2, 3, -4, 5, -6]), 3));
        assert!(c.insert(&lits(&[1, 2, 3, 4, 5, 6]), 7));
        assert!(c.find(&lits(&[1, 3]), usize::MAX).is_some());
        assert!(c.find(&lits(&[-2, -4]), usize::MAX).is_some());
        assert!(c.find(&lits(&[2, -4]), usize::MAX).is_none());
        assert!(c.find(&lits(&[-1]), usize::MAX).is_none());
        // Depth filters.
        assert!(c.find(&lits(&[2, 4]), 6).is_none());
        assert!(c.find(&lits(&[2, 4]), 7).is_some());
        let id = c.find(&lits(&[-6]), 3).unwrap();
        assert_eq!(c.depth(id), 3);
        assert!(c.satisfies(id, Lit::from(5)));
        assert!(!c.satisfies(id, Lit::from(6)));
    }

    #[test]
    fn non_latch_literals_never_match() {
        let mut c = cache();
        c.insert(&lits(&[1, 2, 3, 4, 5, 6]), 1);
        assert!(c.find(&lits(&[1, 9]), usize::MAX).is_none());
        assert!(c.find(&lits(&[100]), usize::MAX).is_none());
    }

    #[test]
    fn partial_states_are_conservative() {
        let mut c = cache();
        c.insert(&lits(&[1, -2]), 1);
        assert!(c.find(&lits(&[1]), usize::MAX).is_some());
        // Latch 3 is unknown in the cached state.
        assert!(c.find(&lits(&[1, 3]), usize::MAX).is_none());
        assert!(c.find(&lits(&[1, -3]), usize::MAX).is_none());
    }

    #[test]
    fn duplicates_keep_min_depth() {
        let mut c = cache();
        assert!(c.insert(&lits(&[1, 2, 3, 4, 5, 6]), 5));
        assert!(!c.insert(&lits(&[1, 2, 3, 4, 5, 6]), 2));
        assert_eq!(c.len(), 1);
        assert!(c.find(&lits(&[1]), 2).is_some());
    }

    #[test]
    fn cleanup_bounds_size_and_keeps_hot_states() {
        let mut c = cache();
        let hot = lits(&[1, 2, 3, 4, 5, 6]);
        c.insert(&hot, 1);
        for _ in 0..10 {
            assert!(c.find(&lits(&[1, 2, 3, 4, 5, 6]), usize::MAX).is_some());
        }
        for x in 0..63 {
            let s: LitVec = (0..6)
                .map(|i| Lit::new(Var::new(i + 1), (x >> i) & 1 == 1))
                .collect();
            c.insert(&s, 1);
            assert!(c.len() <= c.capacity());
            // The hot state keeps being used and must survive cleanups.
            assert!(c.find(&hot, usize::MAX).is_some());
        }
        assert!(c.stat.cleanups > 0);
        assert!(c.find(&hot, usize::MAX).is_some());
        // Every surviving state is still found through every one of its literals.
        for id in 0..c.len() {
            let s = c.state_lits(id, &(1..=6).map(Var::new).collect::<Vec<_>>());
            for l in s.iter() {
                assert!(c.find(&[*l], usize::MAX).is_some());
            }
            assert!(c.find(&s, usize::MAX).is_some());
        }
    }
}
