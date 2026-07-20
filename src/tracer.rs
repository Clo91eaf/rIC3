use crate::{
    McBlCertificate, McResult,
    utils::{LemmaIpcRx, LemmaIpcTx, StateIpcTx},
};
use intertrait::{CastFrom, cast::CastBox};
use ipc_channel::TryRecvError;
use log::info;
use logicrs::LitVec;
use std::{
    ops::Deref,
    sync::mpsc::{self, Receiver, Sender},
};

pub trait TracerIf: Sync + Send + CastFrom {}

pub trait StateTracerIf: TracerIf {
    /// Trace a result. prop is None for all properties, Some(id) for a specific property.
    fn trace_state(&mut self, _prop: Option<usize>, _res: McResult) {}
}

pub trait CertTracerIf: TracerIf {
    /// Trace cert
    fn trace_cert(&mut self, _c: &McBlCertificate) {}
}

pub trait LemmaTracerIf: TracerIf {
    /// Trace a lemma for a specific step (`Some(k)`) or for all steps (`None`).
    fn trace_lemma(&mut self, _inv: &LitVec, _k: Option<usize>) {}
}

/// Sender part of state channel tracer
pub struct StateChannelTracerSx(Sender<(Option<usize>, McResult)>);

impl TracerIf for StateChannelTracerSx {}

#[intertrait::cast_to]
impl StateTracerIf for StateChannelTracerSx {
    fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        let _ = self.0.send((prop, res));
    }
}

/// Receiver part of state channel tracer
pub struct StateChannelTracerRx(Receiver<(Option<usize>, McResult)>);

impl Deref for StateChannelTracerRx {
    type Target = Receiver<(Option<usize>, McResult)>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Create a state channel tracer pair (sender, receiver)
pub fn state_channel_tracer() -> (StateChannelTracerSx, StateChannelTracerRx) {
    let (tx, rx) = mpsc::channel();
    (StateChannelTracerSx(tx), StateChannelTracerRx(rx))
}

/// Sender part of witness channel tracer
pub struct WitnessChannelTracerSx(Sender<McBlCertificate>);

impl TracerIf for WitnessChannelTracerSx {}

#[intertrait::cast_to]
impl CertTracerIf for WitnessChannelTracerSx {
    fn trace_cert(&mut self, c: &McBlCertificate) {
        let _ = self.0.send(c.clone());
    }
}

/// Receiver part of witness channel tracer
pub struct WitnessChannelTracerRx(Receiver<McBlCertificate>);

impl Deref for WitnessChannelTracerRx {
    type Target = Receiver<McBlCertificate>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Create a witness channel tracer pair (sender, receiver)
pub fn witness_channel_tracer() -> (WitnessChannelTracerSx, WitnessChannelTracerRx) {
    let (tx, rx) = mpsc::channel();
    (WitnessChannelTracerSx(tx), WitnessChannelTracerRx(rx))
}

#[derive(Default)]
pub struct Tracer {
    state: Vec<Box<dyn StateTracerIf>>,
    cert: Vec<Box<dyn CertTracerIf>>,
    lemma: Vec<Box<dyn LemmaTracerIf>>,
}

impl Tracer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        match tracer.cast::<dyn StateTracerIf>() {
            Ok(t) => self.state.push(t),
            Err(tracer) => match tracer.cast::<dyn CertTracerIf>() {
                Ok(t) => self.cert.push(t),
                Err(tracer) => match tracer.cast::<dyn LemmaTracerIf>() {
                    Ok(t) => self.lemma.push(t),
                    Err(_) => panic!("unsupported tracer type"),
                },
            },
        }
    }

    pub fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        for t in self.state.iter_mut() {
            t.trace_state(prop, res);
        }
    }

    pub fn trace_cert(&mut self, c: &McBlCertificate) {
        for t in self.cert.iter_mut() {
            t.trace_cert(c);
        }
    }

    /// True when at least one lemma tracer (i.e. a portfolio exporter) is
    /// attached; lets engines skip the cost of preparing shared lemmas when
    /// running standalone.
    pub fn wants_lemma(&self) -> bool {
        !self.lemma.is_empty()
    }

    pub fn trace_lemma(&mut self, inv: &LitVec, k: Option<usize>) {
        for t in self.lemma.iter_mut() {
            t.trace_lemma(inv, k);
        }
    }
}

pub struct LogTracer {
    name: String,
    unknown: Option<usize>,
}

impl LogTracer {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            unknown: None,
        }
    }

    pub fn update_unknow(&mut self, d: usize) -> bool {
        match self.unknown {
            None if d == 0 => {
                self.unknown = Some(d);
                true
            }
            Some(l) if d == l + 1 => {
                self.unknown = Some(d);
                true
            }
            _ => false,
        }
    }
}

impl TracerIf for LogTracer {}

#[intertrait::cast_to]
impl StateTracerIf for LogTracer {
    fn trace_state(&mut self, _prop: Option<usize>, res: McResult) {
        match res {
            McResult::UNSAT => info!("{} proved the property", self.name),
            McResult::SAT(d) => info!("{} found a counterexample at depth {d}", self.name),
            McResult::Unknown(Some(d)) => {
                if self.update_unknow(d) {
                    info!("{} found no counterexample up to depth {d}", self.name)
                } else {
                    info!("{} found no counterexample at exact depth {d}", self.name)
                }
            }
            _ => (),
        }
    }
}

impl TracerIf for StateIpcTx {}

#[intertrait::cast_to]
impl StateTracerIf for StateIpcTx {
    fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        let _ = self.send((prop, res));
    }
}

impl TracerIf for LemmaIpcTx {}

#[intertrait::cast_to]
impl LemmaTracerIf for LemmaIpcTx {
    fn trace_lemma(&mut self, inv: &LitVec, k: Option<usize>) {
        let _ = self.send((k, inv.clone()));
    }
}

impl ExtractorIf for LemmaIpcRx {
    fn extract_lemma(&mut self) -> Option<(Option<usize>, LitVec)> {
        match self.try_recv() {
            Ok(r) => Some(r),
            Err(TryRecvError::Empty) => None,
            _ => panic!(),
        }
    }
}

/// Continuously-drained wrapper around an inbound lemma channel.
///
/// `ipc_channel` sends are *blocking* once the OS socket buffer fills. If the
/// engine only polled its inbound channel occasionally (e.g. once per major
/// iteration), that buffer could fill while the engine was busy — and then the
/// portfolio's lemma manager would block trying to forward into it. Because a
/// busy engine is itself blocked exporting into the manager, this closes a
/// worker↔manager cycle and deadlocks the whole portfolio.
///
/// This wrapper spawns a dedicated thread that does nothing but drain the OS
/// buffer (blocking `recv`) into a bounded in-process queue, dropping messages
/// when the queue is full. Lemma sharing is best-effort anyway, so dropping
/// under load is acceptable — and keeping the OS buffer empty guarantees the
/// manager's forwarding sends never block, which breaks the deadlock cycle.
pub struct ThreadedExtractor {
    rx: Receiver<(Option<usize>, LitVec)>,
}

impl ThreadedExtractor {
    pub fn new(ipc: LemmaIpcRx) -> Self {
        // bounded: caps memory if the engine consumes slower than peers produce
        let (tx, rx) = mpsc::sync_channel::<(Option<usize>, LitVec)>(8192);
        std::thread::spawn(move || {
            // `recv` blocks; it returns Err only when every sender is gone,
            // i.e. the channel is torn down at shutdown — then the thread ends.
            while let Ok(msg) = ipc.recv() {
                // best-effort: if the in-process queue is full, drop the lemma
                // but keep draining the OS buffer so the manager never blocks
                let _ = tx.try_send(msg);
            }
        });
        Self { rx }
    }
}

impl ExtractorIf for ThreadedExtractor {
    fn extract_lemma(&mut self) -> Option<(Option<usize>, LitVec)> {
        self.rx.try_recv().ok()
    }
}

pub trait ExtractorIf: Send {
    fn extract_lemma(&mut self) -> Option<(Option<usize>, LitVec)>;
}
