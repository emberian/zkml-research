#!/bin/sh
# Compile the pinned upstream offline verifier and its reserve codecs unchanged.
set -eu
root=$(git rev-parse --show-toplevel)
billing=${1:-/Users/ember/dev/DreggNet}
pin=1d4fad6
mkdir -p "$root/native/target"
work=$(mktemp -d "$root/native/target/billing-interop.XXXXXX")
mkdir -p "$work/src/reserve" "$work/tests"
for file in handoff.rs reserve/mod.rs reserve/store.rs reserve/schema.sql; do
    git -C "$billing" show "$pin:billing/src/$file" > "$work/src/$file"
done
git -C "$billing" show "$pin:billing/tests/handoff.rs" > "$work/tests/handoff.rs"
cat > "$work/src/lib.rs" <<'RS'
pub mod handoff;
pub mod reserve;
RS
cat > "$work/Cargo.toml" <<'TOML'
[workspace]

[package]
name = "dreggnet-billing"
version = "0.0.0"
edition = "2024"

[dependencies]
resident_custody = { path = "../../resident_custody" }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
sha2 = "0.10"
blake3 = "1"
hex = "0.4"
ed25519-dalek = "2"
thiserror = "2"
rusqlite = { version = "0.32", features = ["bundled"] }
TOML
cat >> "$work/tests/handoff.rs" <<'RS'

#[test]
fn cross_crate_receipts() {
    use resident_custody::seat_receipt as resident;
    let p = policy();
    let target_policy = resident::AdmissionPolicy {
        issuer: p.issuer, target: p.target, asset: p.asset, currency: p.currency,
        epoch_floor: p.epoch_floor, max_reserve_cap_minor: p.max_reserve_cap_minor,
    };
    let mut three = transfer();
    three.credits.push(credit(claim("pi_z", "evt_z", 3), 0,
        CreditBacking::Settled { deposit_sha256: sha256(b"deposit-z") }));
    for t in [transfer(), three] {
        let upstream_wire = sealed(t.clone());
        let resident_receipt = resident::SeatTransferReceipt::verify(&upstream_wire, &target_policy).unwrap();
        let resident_wire = resident::SeatTransferReceipt::seal(resident_receipt.transfer, &source_key())
            .unwrap().to_bytes().unwrap();
        assert_eq!(verify(&resident_wire).unwrap().transfer, t);
        assert_eq!(upstream_wire, resident_wire);
    }
}
RS
cd "$work"
CARGO_TARGET_DIR="$root/native/target" RUSTFLAGS='-D warnings' cargo test --release --test handoff
