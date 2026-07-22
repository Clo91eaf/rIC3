use crate::utils::{LemmaIpcRx, LemmaIpcTx};
use giputils::hash::GHashMap;
use ipc_channel::ipc::{IpcReceiverSet, IpcSelectionResult};
use logicrs::LitVec;
use std::io;

pub struct LemmaMgr {
    recv: IpcReceiverSet,
    rid_to_wid: GHashMap<u64, usize>,
    workers: Vec<LemmaWorker>,
    stop_id: u64,
}

struct LemmaWorker {
    #[allow(unused)]
    name: String,
    /// workers sharing a group key have an identical transition system (same
    /// preprocessing and system-transforming flags), so their frames are
    /// comparable. Lemmas are forwarded only within a group.
    group: String,
    send: LemmaIpcTx,
}

impl LemmaMgr {
    /// Returns the manager together with a shutdown sender: the manager holds
    /// send ends of the very channels its select set receives on, so channel
    /// closure alone can never terminate `run` — the coordinator must signal
    /// shutdown explicitly before joining.
    pub fn new() -> (Self, LemmaIpcTx) {
        let mut recv = IpcReceiverSet::new().unwrap();
        let (stop_tx, stop_rx) = ipc_channel::ipc::channel().unwrap();
        let stop_id = recv.add(stop_rx).unwrap();
        (
            Self {
                recv,
                rid_to_wid: GHashMap::new(),
                workers: Vec::new(),
                stop_id,
            },
            stop_tx,
        )
    }

    pub fn add_worker(
        &mut self,
        worker: String,
        group: String,
        recv: LemmaIpcRx,
        send: LemmaIpcTx,
    ) -> io::Result<()> {
        let recv_id = self.recv.add(recv)?;
        let worker_idx = self.workers.len();
        self.rid_to_wid.insert(recv_id, worker_idx);
        self.workers.push(LemmaWorker {
            name: worker,
            group,
            send,
        });
        Ok(())
    }

    pub fn run(mut self) {
        loop {
            match self.recv.select() {
                Ok(events) => {
                    for event in events {
                        match event {
                            IpcSelectionResult::MessageReceived(id, message) => {
                                if id == self.stop_id {
                                    return;
                                }
                                let Some(&worker_idx) = self.rid_to_wid.get(&id) else {
                                    continue;
                                };
                                let (k, lemma): (Option<usize>, LitVec) = message.to().unwrap();
                                // Only forward a lemma to workers in the source's
                                // group — those with an identical transition
                                // system. Engines like `--inn` (internal signals)
                                // or `--abs-*` reason over a *transformed* system,
                                // so even their inductive invariants are not valid
                                // clauses for a differently-configured worker;
                                // cross-group sharing can inject an unsound lemma
                                // and yield a false UNSAT.
                                let src_group = &self.workers[worker_idx].group;
                                let mut sent = 0usize;
                                for (idx, other) in self.workers.iter().enumerate() {
                                    if idx == worker_idx || &other.group != src_group {
                                        continue;
                                    }
                                    let _ = other.send.send((k, lemma.clone()));
                                    sent += 1;
                                }
                                if std::env::var("RIC3_SHARE_DEBUG").is_ok() {
                                    eprintln!(
                                        "lemma-mgr: recv w{worker_idx} k={k:?} len={} group='{src_group}' -> {sent} recipients",
                                        lemma.len()
                                    );
                                }
                            }
                            IpcSelectionResult::ChannelClosed(id) => {
                                self.rid_to_wid.remove(&id);
                            }
                        }
                    }
                }
                Err(_) => {
                    return;
                }
            }
        }
    }
}
