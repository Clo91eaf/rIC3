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
        recv: LemmaIpcRx,
        send: LemmaIpcTx,
    ) -> io::Result<()> {
        let recv_id = self.recv.add(recv)?;
        let worker_idx = self.workers.len();
        self.rid_to_wid.insert(recv_id, worker_idx);
        self.workers.push(LemmaWorker { name: worker, send });
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
                                for (idx, other) in self.workers.iter().enumerate() {
                                    if idx == worker_idx {
                                        continue;
                                    }
                                    let _ = other.send.send((k, lemma.clone()));
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
