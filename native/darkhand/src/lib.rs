//! The custody handover as custodian processes (gen 6). `erase`: the zeroizing allocator, explicit wipes and file
//! wipes. `scan`: a custodian's scan of its own address space for its secret material (Linux /proc). `ceremony`: the
//! new committee's key ceremony at its own epoch. `side`: what an old and a new custodian process do at the
//! handover (resharing over the six-party mesh, the joint proof, re-authentication, erasure).
pub mod ceremony;
pub mod erase;
pub mod scan;
pub mod serve;
pub mod side;
