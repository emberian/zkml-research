//! Comprehensive conformance & adversarial attack suite for `quarried_shells`.
//!
//! Verifies:
//! 1. All 25 `ViewNode` variants: canonical `DVN1` binary codec roundtrip, DoS/tamper/trailing-byte
//!    rejection, progressive `disclose`, and `format_value`.
//! 2. Deterministic tree diff/patch roundtrip across all 25 variants + fail-closed mismatch refusal.
//! 3. `Frustum` fog-of-war non-interference across `Sever`, `Attenuate`, `Interpose`, and `Tether`,
//!    plus non-vacuity `#tooth` test.
//! 4. `synthesize_repair_badge` & `evaluate_affordance` parity with `Obend.Vault.Affordance`.
//! 5. `S11`-hardened Electra (`397/512` & `342/512` golden vectors matching Lean + real SSZ Merkle
//!    branches) & attack refusals (cross-chain, future-slot, stale, `341/512`, wrong fork digest,
//!    period drift, finalized rollback, tampered Merkle branch).
//! 6. `S11`-hardened CometBFT (`cosmoshub-4` adjacent & `95`-block skip matching Lean) + two-level
//!    ICS-23 `bank` balance envelope -> sealed `ProvenForeignHolding` (`S8` closed) + attack refusals.

use std::collections::{BTreeMap, BTreeSet};

use quarried_shells::lightclient_gate::{
    compute_fork_digest, compute_ics23_root, cosmos_denom_asset_id, decode_bank_balance_kv,
    is_valid_merkle_branch, period_of_slot, sha256, sha256_pair, verify_comet_header_s11,
    verify_cosmos_bank_balance_envelope, verify_eth_header_s11, CometAdvanceMode, CometGateError,
    CometHeaderUpdate, CometTrustAnchor, EnvelopeError, EthGateError, EthHeaderUpdate,
    EthTrustAnchor, Ics23ExistenceProof, Ics23InnerOp, Ics23LeafOp, Ics23TwoLevelProof,
    BALANCES_PREFIX, BANK_STORE_KEY, COSMOS_CHAIN_TAG, EXECUTION_PAYLOAD_DEPTH,
    EXECUTION_PAYLOAD_SUBTREE_INDEX, FINALIZED_ROOT_DEPTH_ALTAIR, FINALIZED_ROOT_DEPTH_ELECTRA,
    FINALIZED_ROOT_SUBTREE_INDEX, SYNC_COMMITTEE_SIZE,
};
use quarried_shells::viewnode_ir::{
    apply_patch, diff, disclose, evaluate_affordance, format_value, project_view_node,
    synthesize_repair_badge, AffordanceStatus, BindFmt, CodecError, ContainerTag, CoordCell, Crumb,
    Disclosure, Disposition, Frustum, HaloHandle, HostStatus, MenuItem, PatchError, PillCase,
    ViewNode, ViewPatch, WorldState, MAX_VIEW_DEPTH,
};

// ---------------------------------------------------------------------------
// Helpers for constructing all 25 ViewNode variants and valid Merkle branches
// ---------------------------------------------------------------------------

fn all_25_variants() -> Vec<ViewNode> {
    vec![
        ViewNode::VStack(vec![ViewNode::Text("v".into())]),
        ViewNode::Row(vec![ViewNode::Divider]),
        ViewNode::Text("hello world".into()),
        ViewNode::Bind {
            slot: 3,
            label: "balance".into(),
            fmt: BindFmt::Amount,
            resolved: Some(1_234_567),
        },
        ViewNode::Button {
            label: "Submit".into(),
            turn: "vote".into(),
            arg: -7,
        },
        ViewNode::Input {
            bind_view: "draft_title".into(),
            fire_turn: "set_title".into(),
            submit_label: "Save".into(),
        },
        ViewNode::List(vec![ViewNode::Text("item 0".into())]),
        ViewNode::Table(vec![ViewNode::Row(vec![ViewNode::Text("cell".into())])]),
        ViewNode::Section {
            title: "Vault".into(),
            tag: "genuine".into(),
            children: vec![ViewNode::Divider],
        },
        ViewNode::Tabs {
            tabs: vec!["Inhabit".into(), "Inspect".into()],
            selected_slot: 1,
            select_turn: "select_tab".into(),
            resolved_active: Some(0),
            panels: vec![ViewNode::Text("p0".into()), ViewNode::Text("p1".into())],
        },
        ViewNode::Gauge {
            slot: 4,
            max: 100,
            label: "liveness".into(),
            resolved: Some(85),
        },
        ViewNode::Divider,
        ViewNode::Host {
            cell: "cell-alpha".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Text("hosted".into()))),
        },
        ViewNode::Grid {
            cols: 3,
            children: vec![ViewNode::Icon {
                glyph: "✦".into(),
                tag: "accent".into(),
            }],
        },
        ViewNode::Breadcrumb {
            items: vec![
                Crumb {
                    label: "Root".into(),
                    turn: "nav".into(),
                    arg: 0,
                },
                Crumb {
                    label: "Leaf".into(),
                    turn: String::new(),
                    arg: 1,
                },
            ],
        },
        ViewNode::Progress {
            value: 3,
            max: 5,
            label: "sync".into(),
        },
        ViewNode::Pill {
            text: "COMMIT".into(),
            tag: "warn".into(),
            slot: Some(2),
            cases: vec![
                PillCase {
                    value: 0,
                    label: "COMMIT".into(),
                    tag: "warn".into(),
                },
                PillCase {
                    value: 1,
                    label: "RESOLVED".into(),
                    tag: "good".into(),
                },
            ],
            resolved: Some(1),
        },
        ViewNode::Icon {
            glyph: "✓".into(),
            tag: "good".into(),
        },
        ViewNode::Menu {
            items: vec![
                MenuItem {
                    label: "Edit".into(),
                    turn: "edit_doc".into(),
                    arg: 1,
                    enabled: true,
                    wants_text: true,
                },
                MenuItem {
                    label: "Delete".into(),
                    turn: "del_doc".into(),
                    arg: 2,
                    enabled: false,
                    wants_text: false,
                },
            ],
        },
        ViewNode::Halo {
            target_slot: 9,
            handles: vec![HaloHandle {
                glyph: "⚙".into(),
                turn: "inspect".into(),
                arg: 9,
                enabled: true,
            }],
        },
        ViewNode::Slider {
            slot: 5,
            min: 0,
            max: 1000,
            turn: "seek".into(),
            resolved: Some(420),
        },
        ViewNode::Toggle {
            slot: 6,
            on_turn: "enable".into(),
            off_turn: "disable".into(),
            glyph_on: "✓".into(),
            glyph_off: "○".into(),
            label: "Cull".into(),
            resolved: Some(1),
        },
        ViewNode::Tile {
            handle: "svg-workbook-0".into(),
            w: 640,
            h: 480,
        },
        ViewNode::CoordGrid {
            cols: 2,
            cells: vec![
                CoordCell {
                    glyph: "♔".into(),
                    tag: "good".into(),
                    turn: "move".into(),
                    arg: 0,
                    highlight: true,
                },
                CoordCell {
                    glyph: "·".into(),
                    tag: "muted".into(),
                    turn: String::new(),
                    arg: 1,
                    highlight: false,
                },
            ],
        },
        ViewNode::Adept(Box::new(ViewNode::Text("raw-hash:0xdeadbeef".into()))),
    ]
}

fn build_merkle_root(leaf: &[u8; 32], branch: &[[u8; 32]], index: u64) -> [u8; 32] {
    let mut acc = *leaf;
    for (i, sib) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            acc = sha256_pair(sib, &acc);
        } else {
            acc = sha256_pair(&acc, sib);
        }
    }
    acc
}

fn golden_eth_anchor() -> EthTrustAnchor {
    // Matches Minidregg.Assurance.LightClientAndViewLens.goldenEthAnchor
    EthTrustAnchor {
        expected_chain_id: 1,
        expected_fork_digest: 0x6A95_A1A9,
        current_period: 1800,
        trusted_attested_slot: 14_745_600,
        trusted_finalized_slot: 14_745_536,
        max_staleness: 3600,
        max_clock_drift: 60,
    }
}

fn golden_eth_update_electra_397() -> EthHeaderUpdate {
    let finalized_beacon_root = sha256(b"mainnet-period-1800-finalized-beacon-header");
    let finality_branch: Vec<[u8; 32]> = (0..FINALIZED_ROOT_DEPTH_ELECTRA)
        .map(|i| sha256(&[0xF0, i as u8]))
        .collect();
    let attested_state_root = build_merkle_root(
        &finalized_beacon_root,
        &finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
    );

    let execution_payload_root = sha256(b"mainnet-period-1800-exec-payload-header");
    let execution_branch: Vec<[u8; 32]> = (0..EXECUTION_PAYLOAD_DEPTH)
        .map(|i| sha256(&[0xE0, i as u8]))
        .collect();
    let finalized_body_root = build_merkle_root(
        &execution_payload_root,
        &execution_branch,
        EXECUTION_PAYLOAD_SUBTREE_INDEX,
    );
    let execution_state_root = sha256(b"mainnet-period-1800-evm-state-root");

    EthHeaderUpdate {
        chain_id: 1,
        fork_digest: 0x6A95_A1A9,
        attested_slot: 14_745_664,
        signature_slot: 14_745_665,
        finalized_slot: 14_745_600,
        attested_time: 1_780_000_000,
        committee_len: SYNC_COMMITTEE_SIZE,
        bits_len: SYNC_COMMITTEE_SIZE,
        participant_count: 397,
        bls_agg_ok: true,
        attested_state_root,
        finalized_beacon_root,
        finality_branch,
        finalized_body_root,
        execution_payload_root,
        execution_branch,
        execution_state_root,
    }
}

fn golden_comet_anchor() -> CometTrustAnchor {
    // Matches Minidregg.Assurance.LightClientAndViewLens.goldenCometAnchor
    CometTrustAnchor {
        expected_chain_id: "cosmoshub-4".into(),
        expected_fork_digest: 0xC054_0504,
        trusted_height: 26_000_000,
        trusted_header_time: 1_780_000_000,
        trusting_period: 1_209_600,
        max_staleness: 3600,
        max_clock_drift: 60,
    }
}

fn golden_comet_adjacent(app_hash: [u8; 32]) -> CometHeaderUpdate {
    CometHeaderUpdate {
        chain_id: "cosmoshub-4".into(),
        fork_digest: 0xC054_0504,
        height: 26_000_001,
        header_time: 1_780_000_006,
        app_hash,
        epoch_bind_ok: true,
        self_bind_ok: true,
        commit_matches_header: true,
        total_power: 300,
        signed_power: 201,
        trusted_total_power: 300,
        trusted_signed_power: 201,
    }
}

fn golden_comet_skip95(app_hash: [u8; 32]) -> CometHeaderUpdate {
    CometHeaderUpdate {
        chain_id: "cosmoshub-4".into(),
        fork_digest: 0xC054_0504,
        height: 26_000_095,
        header_time: 1_780_000_570,
        app_hash,
        epoch_bind_ok: false,
        self_bind_ok: true,
        commit_matches_header: true,
        total_power: 300,
        signed_power: 240,
        trusted_total_power: 300,
        trusted_signed_power: 101,
    }
}

// ---------------------------------------------------------------------------
// 1. ViewNode 25-Variant Codec, Disclosure, Format & Diff/Patch Tests
// ---------------------------------------------------------------------------

#[test]
fn viewnode_all_25_variants_binary_codec_roundtrip() {
    let variants = all_25_variants();
    assert_eq!(variants.len(), 25);

    let mut seen_tags = BTreeSet::new();
    for node in &variants {
        assert!(seen_tags.insert(node.variant_tag()));
        let bytes = node.encode().expect("encode");
        let decoded = ViewNode::decode(&bytes).expect("decode");
        assert_eq!(&decoded, node);
    }
    assert_eq!(seen_tags.len(), 25);

    let root = ViewNode::VStack(variants);
    let encoded = root.encode().expect("encode full tree");
    assert_eq!(ViewNode::decode(&encoded).expect("decode full tree"), root);

    // Trailing bytes refused
    let mut with_trailing = encoded.clone();
    with_trailing.push(0x00);
    assert_eq!(
        ViewNode::decode(&with_trailing),
        Err(CodecError::TrailingBytes(1))
    );

    // Truncated stream refused
    assert_eq!(
        ViewNode::decode(&encoded[..encoded.len() - 1]),
        Err(CodecError::UnexpectedEof)
    );

    // Bad magic refused
    let mut bad_magic = encoded;
    bad_magic[0] = b'X';
    assert_eq!(ViewNode::decode(&bad_magic), Err(CodecError::BadMagic));
}

#[test]
fn viewnode_codec_enforces_depth_limit() {
    let mut deep = ViewNode::Divider;
    for _ in 0..=MAX_VIEW_DEPTH + 1 {
        deep = ViewNode::Adept(Box::new(deep));
    }
    assert!(matches!(deep.encode(), Err(CodecError::DepthExceeded(_))));
}

#[test]
fn viewnode_disclose_and_format_value() {
    let tree = ViewNode::VStack(vec![
        ViewNode::Text("visible".into()),
        ViewNode::Adept(Box::new(ViewNode::Text("internal".into()))),
    ]);
    assert_eq!(
        disclose(&tree, Disclosure::Simple),
        ViewNode::VStack(vec![ViewNode::Text("visible".into())])
    );
    assert_eq!(
        disclose(&tree, Disclosure::Adept),
        ViewNode::VStack(vec![
            ViewNode::Text("visible".into()),
            ViewNode::Text("internal".into()),
        ])
    );
    assert_eq!(format_value(1_234_567, BindFmt::Amount), "1,234,567");
    assert_eq!(
        format_value(0x8bf3_0000_0000_a3d8, BindFmt::Hex),
        "0x8bf3…a3d8"
    );
    assert!(!format_value(42, BindFmt::Id).is_empty());
}

#[test]
fn viewnode_diff_patch_roundtrip_and_mismatch_tooth() {
    let variants = all_25_variants();
    for v in &variants {
        assert_eq!(diff(v, v), ViewPatch::Keep);
        assert_eq!(apply_patch(v, &ViewPatch::Keep), Ok(v.clone()));
    }
    for i in 0..variants.len() {
        let j = (i + 7) % variants.len();
        let p = diff(&variants[i], &variants[j]);
        assert_eq!(apply_patch(&variants[i], &p), Ok(variants[j].clone()));
    }

    // Structural minimal patch inside matching container preserves sibling via Keep
    let a = ViewNode::VStack(vec![
        ViewNode::Text("stable".into()),
        ViewNode::Bind {
            slot: 0,
            label: "count".into(),
            fmt: BindFmt::Raw,
            resolved: Some(1),
        },
    ]);
    let b = ViewNode::VStack(vec![
        ViewNode::Text("stable".into()),
        ViewNode::Bind {
            slot: 0,
            label: "count".into(),
            fmt: BindFmt::Raw,
            resolved: Some(2),
        },
    ]);
    let patch = diff(&a, &b);
    assert!(matches!(
        &patch,
        ViewPatch::PatchContainer {
            tag: ContainerTag::VStack,
            patches
        } if patches.len() == 2 && patches[0] == ViewPatch::Keep
    ));
    assert_eq!(apply_patch(&a, &patch), Ok(b));

    // #tooth: mismatched container patch fails closed
    let bad = apply_patch(
        &ViewNode::Row(vec![ViewNode::Text("a".into())]),
        &ViewPatch::PatchContainer {
            tag: ContainerTag::VStack,
            patches: vec![ViewPatch::Keep],
        },
    );
    assert_eq!(bad, Err(PatchError::ContainerMismatch));
}

// ---------------------------------------------------------------------------
// 2. Frustum Fog-of-War Non-Interference & Repair Badge Tests
// ---------------------------------------------------------------------------

#[test]
fn frustum_fog_of_war_noninterference_and_nonvacuity_tooth() {
    let mut visible = BTreeSet::new();
    visible.insert(("root".to_owned(), 0usize));
    visible.insert(("shared-doc".to_owned(), 1usize));
    visible.insert(("shared-doc".to_owned(), 2usize));
    visible.insert(("tethered-card".to_owned(), 0usize));

    let mut allowed_shared = BTreeSet::new();
    allowed_shared.insert(("shared-doc".to_owned(), 1usize)); // slot 2 attenuated away!

    let mut policies = BTreeMap::new();
    policies.insert(
        "vault-secret".to_owned(),
        Disposition::Sever {
            snapshot_digest: 0xBEEF,
        },
    );
    policies.insert(
        "mock-oracle".to_owned(),
        Disposition::Interpose {
            mock_label: "cached-price".into(),
        },
    );
    policies.insert(
        "shared-doc".to_owned(),
        Disposition::Attenuate {
            allowed_slots: allowed_shared,
        },
    );
    policies.insert("tethered-card".to_owned(), Disposition::Tether);

    let frustum = Frustum {
        viewer: "alice".into(),
        visible_slots: visible,
        policies,
    };

    let tree = ViewNode::VStack(vec![
        ViewNode::Bind {
            slot: 0,
            label: "public_balance".into(),
            fmt: BindFmt::Amount,
            resolved: None,
        },
        ViewNode::Host {
            cell: "vault-secret".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Bind {
                slot: 7,
                label: "private_key_share".into(),
                fmt: BindFmt::Hex,
                resolved: None,
            })),
        },
        ViewNode::Host {
            cell: "mock-oracle".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Gauge {
                slot: 2,
                max: 100,
                label: "oracle".into(),
                resolved: None,
            })),
        },
        ViewNode::Host {
            cell: "shared-doc".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Row(vec![
                ViewNode::Bind {
                    slot: 1,
                    label: "allowed".into(),
                    fmt: BindFmt::Raw,
                    resolved: None,
                },
                ViewNode::Bind {
                    slot: 2,
                    label: "attenuated_secret".into(),
                    fmt: BindFmt::Raw,
                    resolved: None,
                },
            ]))),
        },
        ViewNode::Host {
            cell: "tethered-card".into(),
            status: HostStatus::Live,
            view: Some(Box::new(ViewNode::Bind {
                slot: 0,
                label: "live_peer".into(),
                fmt: BindFmt::Raw,
                resolved: None,
            })),
        },
    ]);

    let mut w1 = WorldState::default();
    w1.set("root", 0, 1000);
    w1.set("vault-secret", 7, 42);
    w1.set("mock-oracle", 2, 77);
    w1.set("shared-doc", 1, 10);
    w1.set("shared-doc", 2, 111);
    w1.set("tethered-card", 0, 5);

    // Mutate severed secret, interposed oracle, and attenuated slot arbitrarily
    let mut w2 = w1.clone();
    w2.set("vault-secret", 7, 999_999);
    w2.set("mock-oracle", 2, 12);
    w2.set("shared-doc", 2, 888_888);

    let p1 = project_view_node(&frustum, &w1, "root", &tree);
    let p2 = project_view_node(&frustum, &w2, "root", &tree);
    assert_eq!(p1, p2);
    assert_eq!(p1.encode().unwrap(), p2.encode().unwrap());

    // #tooth non-vacuity: mutating visible slot ("root", 0) MUST change the projection
    let mut w3 = w1;
    w3.set("root", 0, 2500);
    let p3 = project_view_node(&frustum, &w3, "root", &tree);
    assert_ne!(p1, p3);
}

#[test]
fn repair_badge_synthesis_cases() {
    let req = vec!["cap.write".to_owned(), "cap.sign".to_owned()];
    let held_partial = vec!["cap.write".to_owned()];

    let b_missing = synthesize_repair_badge("publish", &req, &held_partial, true, None, "");
    assert_eq!(b_missing.missing_caps, vec!["cap.sign".to_owned()]);
    assert_eq!(
        b_missing.reason,
        "unauthorized: missing required capabilities"
    );

    let b_law = synthesize_repair_badge(
        "publish",
        &req,
        &req,
        false,
        Some(vec![("quorum".into(), 3)]),
        "raise quorum to 3",
    );
    assert!(b_law.missing_caps.is_empty());
    assert_eq!(b_law.repair_edits, Some(vec![("quorum".into(), 3)]));

    let b_both = synthesize_repair_badge(
        "publish",
        &req,
        &held_partial,
        false,
        Some(vec![("quorum".into(), 3)]),
        "acquire cap.sign and raise quorum",
    );
    assert_eq!(b_both.reason, "unauthorized and state contract violated");

    assert_eq!(
        evaluate_affordance("publish", &req, &req, true, None, ""),
        AffordanceStatus::Lit {
            turn: "publish".into()
        }
    );
}

// ---------------------------------------------------------------------------
// 3. SHA-256 KAT & Electra S11 Conformance + Attack Suite
// ---------------------------------------------------------------------------

#[test]
fn sha256_nist_kats_and_fork_digest_domain_separation() {
    // FIPS 180-4 KAT: SHA-256("abc")
    let expected_abc: [u8; 32] = [
        0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22,
        0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00,
        0x15, 0xad,
    ];
    assert_eq!(sha256(b"abc"), expected_abc);

    // Fork digest changes across chains and fork versions
    let gvr = sha256(b"mainnet-genesis");
    let d1 = compute_fork_digest(1, [0x05, 0x00, 0x00, 0x00], &gvr);
    let d2 = compute_fork_digest(11_155_111, [0x05, 0x00, 0x00, 0x00], &gvr);
    let d3 = compute_fork_digest(1, [0x06, 0x00, 0x00, 0x00], &gvr);
    assert_ne!(d1, d2);
    assert_ne!(d1, d3);
    assert_eq!(period_of_slot(14_745_665), 1800);
}

#[test]
fn eth_s11_golden_accepts_and_attack_refusals() {
    let anchor = golden_eth_anchor();
    let u = golden_eth_update_electra_397();
    let host_now = 1_780_000_120;

    // Mainnet Electra 397/512 golden accept
    let verified = verify_eth_header_s11(&anchor, &u, host_now).expect("397/512 Electra accepts");
    assert_eq!(verified.chain_id(), 1);
    assert_eq!(verified.finalized_slot(), 14_745_600);
    assert_eq!(verified.execution_state_root(), u.execution_state_root);

    // Exact 342/512 supermajority floor accepts
    let mut u_342 = u.clone();
    u_342.participant_count = 342;
    assert!(verify_eth_header_s11(&anchor, &u_342, host_now).is_ok());

    // Altair..Deneb depth-6 finality branch also accepted when valid
    let mut u_altair = u.clone();
    u_altair.finality_branch = (0..FINALIZED_ROOT_DEPTH_ALTAIR)
        .map(|i| sha256(&[0xA0, i as u8]))
        .collect();
    u_altair.attested_state_root = build_merkle_root(
        &u_altair.finalized_beacon_root,
        &u_altair.finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
    );
    assert!(is_valid_merkle_branch(
        &u_altair.finalized_beacon_root,
        &u_altair.finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
        &u_altair.attested_state_root
    ));
    assert!(verify_eth_header_s11(&anchor, &u_altair, host_now).is_ok());

    // Attack 1: Cross-chain replay (Sepolia chain_id = 11155111)
    let mut cross = u.clone();
    cross.chain_id = 11_155_111;
    assert_eq!(
        verify_eth_header_s11(&anchor, &cross, host_now),
        Err(EthGateError::ChainIdMismatch)
    );

    // Attack 2: Fork-digest mismatch
    let mut bad_fork = u.clone();
    bad_fork.fork_digest ^= 1;
    assert_eq!(
        verify_eth_header_s11(&anchor, &bad_fork, host_now),
        Err(EthGateError::ForkDigestMismatch)
    );

    // Attack 3: Future/inverted slot spoof (signature_slot < attested_slot)
    let mut bad_sig_slot = u.clone();
    bad_sig_slot.signature_slot = bad_sig_slot.attested_slot - 1;
    assert_eq!(
        verify_eth_header_s11(&anchor, &bad_sig_slot, host_now),
        Err(EthGateError::FutureSlotSpoof)
    );

    // Attack 4: S11 period-bookkeeping drift (slot from period 1801 on period-1800 anchor)
    let mut bad_period = u.clone();
    bad_period.signature_slot = 1801 * 8192;
    assert_eq!(
        verify_eth_header_s11(&anchor, &bad_period, host_now),
        Err(EthGateError::PeriodMismatch)
    );

    // Attack 5: Finalized height rollback
    let mut rollback = u.clone();
    rollback.finalized_slot = anchor.trusted_finalized_slot - 1;
    assert_eq!(
        verify_eth_header_s11(&anchor, &rollback, host_now),
        Err(EthGateError::FinalizedHeightRollback)
    );

    // Attack 6: Expired staleness (host_now = attested_time + max_staleness + 1)
    assert_eq!(
        verify_eth_header_s11(&anchor, &u, u.attested_time + anchor.max_staleness + 1),
        Err(EthGateError::StaleHeader)
    );

    // Attack 7: Future timestamp spoof (attested_time > host_now + max_clock_drift)
    assert_eq!(
        verify_eth_header_s11(&anchor, &u, u.attested_time - anchor.max_clock_drift - 1),
        Err(EthGateError::FutureTimestampSpoof)
    );

    // Attack 8: Sub-supermajority 341/512 & Nomad-law 0/512
    let mut u_341 = u.clone();
    u_341.participant_count = 341;
    assert_eq!(
        verify_eth_header_s11(&anchor, &u_341, host_now),
        Err(EthGateError::InsufficientParticipation)
    );
    let mut u_zero = u.clone();
    u_zero.participant_count = 0;
    assert_eq!(
        verify_eth_header_s11(&anchor, &u_zero, host_now),
        Err(EthGateError::ZeroParticipants)
    );

    // Attack 9: Tampered finality branch & tampered execution branch
    let mut bad_fin = u.clone();
    bad_fin.finality_branch[0][0] ^= 0xff;
    assert_eq!(
        verify_eth_header_s11(&anchor, &bad_fin, host_now),
        Err(EthGateError::BadFinalityBranch)
    );
    let mut bad_exec = u;
    bad_exec.execution_branch[0][0] ^= 0xff;
    assert_eq!(
        verify_eth_header_s11(&anchor, &bad_exec, host_now),
        Err(EthGateError::BadExecutionBranch)
    );
}

// ---------------------------------------------------------------------------
// 4. CometBFT S11 Conformance, ICS-23 Two-Level Bank Envelope & Attacks
// ---------------------------------------------------------------------------

fn build_valid_bank_ics23_proof(address: &[u8], denom: &str, amount: &str) -> ([u8; 32], Ics23TwoLevelProof) {
    let mut key = Vec::new();
    key.push(BALANCES_PREFIX);
    key.push(address.len() as u8);
    key.extend_from_slice(address);
    key.extend_from_slice(denom.as_bytes());

    let sub_proof = Ics23ExistenceProof {
        key,
        value: amount.as_bytes().to_vec(),
        leaf: Ics23LeafOp {
            prefix: vec![0x00, 0x02, 0x02],
            prehash_value: true,
        },
        path: vec![Ics23InnerOp {
            prefix: vec![0x02, 0x04, 0x20],
            suffix: sha256(b"iavl-sibling-0").to_vec(),
        }],
    };
    let store_root = compute_ics23_root(&sub_proof);

    let root_proof = Ics23ExistenceProof {
        key: BANK_STORE_KEY.to_vec(),
        value: store_root.to_vec(),
        leaf: Ics23LeafOp {
            prefix: vec![0x00],
            prehash_value: true,
        },
        path: vec![Ics23InnerOp {
            prefix: vec![0x01, 0x20],
            suffix: sha256(b"multistore-sibling-0").to_vec(),
        }],
    };
    let app_hash = compute_ics23_root(&root_proof);
    (
        app_hash,
        Ics23TwoLevelProof {
            store_key: BANK_STORE_KEY.to_vec(),
            store_root,
            sub_proof,
            root_proof,
        },
    )
}

#[test]
fn comet_s11_golden_accepts_ics23_envelope_and_attacks() {
    let anchor = golden_comet_anchor();
    let addr = [0x42u8; 20];
    let (app_hash, proof) = build_valid_bank_ics23_proof(&addr, "uatom", "331305561223899");

    // Adjacent golden accept
    let adj = golden_comet_adjacent(app_hash);
    let verified_adj =
        verify_comet_header_s11(&anchor, &adj, 1_780_000_020).expect("adjacent accepts");
    assert_eq!(verified_adj.mode(), CometAdvanceMode::Adjacent);
    assert_eq!(verified_adj.chain_id(), "cosmoshub-4");

    // 95-block skip golden accept + sealed ProvenForeignHolding via 2-level ICS-23 proof
    let skip = golden_comet_skip95(app_hash);
    let verified_skip =
        verify_comet_header_s11(&anchor, &skip, 1_780_000_600).expect("95-block skip accepts");
    assert_eq!(verified_skip.mode(), CometAdvanceMode::Skipping);

    let holding = verify_cosmos_bank_balance_envelope(&verified_skip, &proof)
        .expect("valid 2-level ICS-23 bank balance mints sealed holding");
    assert_eq!(holding.chain_tag(), COSMOS_CHAIN_TAG);
    assert_eq!(holding.chain_id(), "cosmoshub-4");
    assert_eq!(holding.amount(), 331_305_561_223_899);
    assert_eq!(holding.snapshot_height(), 26_000_095);
    assert_eq!(holding.asset(), cosmos_denom_asset_id("uatom"));
    assert!(holding.consensus_proven());

    // Attack 1: Cross-chain replay
    let mut cross = adj.clone();
    cross.chain_id = "theta-testnet-001".into();
    assert_eq!(
        verify_comet_header_s11(&anchor, &cross, 1_780_000_020),
        Err(CometGateError::ChainIdMismatch)
    );

    // Attack 2: Expired trusting period
    assert_eq!(
        verify_comet_header_s11(
            &anchor,
            &adj,
            anchor.trusted_header_time + anchor.trusting_period
        ),
        Err(CometGateError::TrustedStateExpired)
    );

    // Attack 3: Stale header
    assert_eq!(
        verify_comet_header_s11(&anchor, &adj, adj.header_time + anchor.max_staleness + 1),
        Err(CometGateError::StaleHeader)
    );

    // Attack 4: Future timestamp spoof
    assert_eq!(
        verify_comet_header_s11(&anchor, &adj, adj.header_time - anchor.max_clock_drift - 1),
        Err(CometGateError::FutureTimestampSpoof)
    );

    // Attack 5: Exact 2/3 (200/300) rejected — strict > 2/3 required
    let mut two_thirds = adj.clone();
    two_thirds.signed_power = 200;
    assert_eq!(
        verify_comet_header_s11(&anchor, &two_thirds, 1_780_000_020),
        Err(CometGateError::InsufficientVotingPower)
    );

    // Attack 6: Zero-overlap 95-block skip rejected
    let mut zero_overlap = skip;
    zero_overlap.trusted_signed_power = 0;
    assert_eq!(
        verify_comet_header_s11(&anchor, &zero_overlap, 1_780_000_600),
        Err(CometGateError::InsufficientTrustOverlap)
    );

    // Attack 7: Non-increasing height rejected
    let mut same_h = adj;
    same_h.height = anchor.trusted_height;
    assert_eq!(
        verify_comet_header_s11(&anchor, &same_h, 1_780_000_020),
        Err(CometGateError::NonIncreasingHeight)
    );

    // Attack 8: Tampered ICS-23 inner node refused
    let mut bad_proof = proof;
    bad_proof.sub_proof.path[0].suffix[0] ^= 0x01;
    assert_eq!(
        verify_cosmos_bank_balance_envelope(&verified_skip, &bad_proof),
        Err(EnvelopeError::SubProofRootMismatch)
    );

    // Attack 9: Supply-prefix (0x00) spoof & leading-zero amount refused by bank decoder
    let supply_key = [0x00, 0x05, b'u', b'a', b't', b'o', b'm'];
    assert_eq!(
        decode_bank_balance_kv(BANK_STORE_KEY, &supply_key, b"1000"),
        Err(EnvelopeError::NotBalanceKey)
    );
    let mut valid_key = vec![BALANCES_PREFIX, 20];
    valid_key.extend_from_slice(&addr);
    valid_key.extend_from_slice(b"uatom");
    assert_eq!(
        decode_bank_balance_kv(BANK_STORE_KEY, &valid_key, b"0123"),
        Err(EnvelopeError::MalformedAmount)
    );
}
