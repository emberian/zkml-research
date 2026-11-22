#![forbid(unsafe_code)]
//! Standalone Wave-8 quarried shells for `Phase 1` `obend-surfaces` and `obend-lightclients`.
//!
//! - [`viewnode_ir`]: Toolkit-free 25-variant `ViewNode` IR quarried from `breadstuffs/deos-view`,
//!   canonical binary codec, deterministic tree diff/patch, `Frustum` fog-of-war scrubber
//!   (`sever`/`attenuate`/`interpose`/`tether`), and `synthesize_repair_badge`.
//! - [`lightclient_gate`]: `S11`-hardened Electra & CometBFT header admission gates, SSZ Merkle
//!   and 2-level ICS-23 bank-balance envelope verification, and sealed `ProvenForeignHolding`.

pub mod lightclient_gate;
pub mod viewnode_ir;
