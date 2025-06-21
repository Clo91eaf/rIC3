use crate::{
    gipsat::{statistic::SolverStatistic, ts::TransysSolver},
    transys::Transys,
};
use giputils::grc::Grc;
use logicrs::{LitVec, Var};
use std::os::raw::c_int;

#[repr(C)]
pub struct CTransysSolver {
    inner: *mut TransysSolver,
}

#[repr(C)]
pub struct CLitVec {
    inner: *mut LitVec,
}

#[repr(C)]
pub struct CVar {
    inner: *mut Var,
}

#[repr(C)]
pub struct CSolverStatistic {
    inner: *mut SolverStatistic,
}

#[unsafe(no_mangle)]
pub extern "C" fn transys_solver_new(rseed: c_int) -> *mut CTransysSolver {
    let ts = Transys::new();
    let tsctx = Grc::new(ts.ctx());
    let solver = Box::new(TransysSolver::new(&tsctx, true, rseed as u64));
    Box::into_raw(Box::new(CTransysSolver {
        inner: Box::into_raw(solver),
    }))
}


#[unsafe(no_mangle)]
pub fn flip_to_none(ptr: *mut CTransysSolver, cvar: *mut CVar) -> bool {
    let solver = unsafe { &mut *(*ptr).inner };
    let var = unsafe { *(*cvar).inner };
    solver.flip_to_none(var)
}


#[unsafe(no_mangle)]
pub fn domain_has(ptr: *mut CTransysSolver, var: Var) -> bool {
    let solver = unsafe { &mut *(*ptr).inner };
    solver.domain_has(var)
}

// 
// #[unsafe(no_mangle)]
// pub fn set_domain(ptr: *mut CTransysSolver, domain: impl IntoIterator<Item = Lit>) {
//     todo!("fix domain ffi");
//     let solver = unsafe { &mut *(*ptr).inner };
//     solver.set_domain(domain);
// }


#[unsafe(no_mangle)]
pub fn unset_domain(ptr: *mut CTransysSolver) {
    let solver = unsafe { &mut *(*ptr).inner };
    solver.unset_domain();
}


#[unsafe(no_mangle)]
pub fn add_domain(ptr: *mut CTransysSolver, cvar: *mut CVar, deps: bool) {
    let solver = unsafe { &mut *(*ptr).inner };
    let var = unsafe { *(*cvar).inner };
    solver.add_domain(var, deps);
}


#[unsafe(no_mangle)]
pub fn statistic(ptr: *mut CTransysSolver) -> *mut CSolverStatistic {
    let solver = unsafe { &mut *(*ptr).inner };
    let result = Box::new(*solver.statistic());
    Box::into_raw(Box::new(CSolverStatistic {
        inner: Box::into_raw(result),
    }))
}
