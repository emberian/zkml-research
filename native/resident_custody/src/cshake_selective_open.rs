//! Selective openings of a blinded resident cell: the cell root is cSHAKE256 of a frame, a
//! 32-byte blind and the cell, and the proof releases exactly the authorized byte ranges.
//! Every width and frame runs on the extended-witness KKW engine in [`crate::kkw`].
pub(crate) mod circuit;
mod framed;
pub use crate::kkw::{INSTANCES, ONLINE_INSTANCES, PARTIES};
pub(crate) use framed::encode_nat;
pub use framed::{check_ranges, root, statement, Circuit, Statement, DOMAIN};

use crate::Digest;
use anyhow::Result;

/// Prove the authorized projection of a resident cell.
pub fn prove(blind: &Digest, cell: &[u8], st: &Statement) -> Result<Vec<u8>> {
    Circuit::resident(cell.len()).prove(blind, cell, st)
}

pub fn verify(width: usize, permitted: &[(u16, u16)], st: &Statement, proof: &[u8]) -> Result<()> {
    Circuit::resident(width).verify(permitted, st, proof)
}

/// Bind an opening to an additional public statement.
pub fn prove_with_context(
    blind: &Digest,
    cell: &[u8],
    st: &Statement,
    binding: &[u8],
) -> Result<Vec<u8>> {
    Circuit::resident(cell.len()).prove_with(blind, cell, st, binding)
}

/// Verify an opening and its caller-supplied public context.
pub fn verify_with_context(
    width: usize,
    permitted: &[(u16, u16)],
    st: &Statement,
    binding: &[u8],
    proof: &[u8],
) -> Result<()> {
    Circuit::resident(width).verify_with(permitted, st, binding, proof)
}

#[cfg(test)]
mod tests {
    use super::circuit::Cell;
    use super::*;
    use crate::kkw::{self, tests::worst_split, Shape};
    use crate::random_seed;
    use crate::trie_opening::Branch;
    use num_bigint::BigUint;
    use std::time::Instant;

    fn choose(n: usize, k: usize) -> BigUint {
        (0..k).fold(BigUint::from(1u8), |a, i| a * (n - i) / (i + 1))
    }

    #[test]
    fn exact_cheating_splits() {
        for (n, m, t, secure) in [
            (PARTIES, INSTANCES, ONLINE_INSTANCES, true),
            (64, 343, 27, true),
            (128, 352, 24, false),
            (128, 384, 24, false),
            (16, 242, 36, false),
            (32, 285, 30, false),
        ] {
            let (k, num, den) = worst_split(n, m, t);
            assert_eq!((&num << 128) <= den, secure);
            if secure {
                for bad in 0..=t {
                    assert!(
                        choose(t, bad) << 128
                            <= choose(m, bad) * BigUint::from(n).pow((t - bad) as u32)
                    );
                }
            }
            println!("N={n} M={m} tau={t} worst_k={k} escape={num}/{den}");
        }
        // Count actual challenges in a toy game independently of the binomial formula.
        for k in 0..=2 {
            let mut pass = 0;
            for a in 0..4 {
                for b in a + 1..4 {
                    for pa in 0..2 {
                        for pb in 0..2 {
                            if (0..k).all(|j| j == a || j == b)
                                && (a < k || pa == 0)
                                && (b < k || pb == 0)
                            {
                                pass += 1u32;
                            }
                        }
                    }
                }
            }
            assert_eq!(
                BigUint::from(pass) * choose(4, k) * 2u32.pow((2 - k) as u32),
                choose(2, k) * 24u32
            );
        }
    }

    #[test]
    fn worst_case_wire_budget() -> Result<()> {
        // The top tree has two occupied perfect subtrees (512 and 128 leaves). For h
        // punctures in a depth-d perfect tree, each level has at most min(2^level, h)
        // occupied ancestors. Bit reversal attains it.
        fn perfect_frontier(depth: u32, h: usize) -> usize {
            1 + (0..depth).map(|d| (1usize << d).min(h)).sum::<usize>() - h
        }
        assert_eq!(INSTANCES, 512 + 128);
        let mut max = 0;
        for left in 0..=ONLINE_INSTANCES {
            let right = ONLINE_INSTANCES - left;
            let mut hidden: Vec<_> = (0..left)
                .map(|i| (i as u32).reverse_bits() as usize >> 23)
                .chain((0..right).map(|i| 512 + ((i as u32).reverse_bits() as usize >> 25)))
                .collect();
            hidden.sort_unstable();
            let bound = perfect_frontier(9, left) + perfect_frontier(7, right);
            assert_eq!(super::super::kkw::tests::frontier_len(&hidden), bound);
            max = max.max(bound);
        }
        assert_eq!(max, 109);
        // The journal header: a 64-byte cell, 48 projected bytes, one squeeze to a public
        // root. 11 checkpoint pairs and a public row-0 pair commit 388 words.
        let blind = random_seed()?;
        let st = statement(
            &blind,
            &[0; 64],
            vec![(0, crate::custody_mesh::HEADER_BYTES)],
        )?;
        let resident = Circuit::resident(64);
        let shape = Shape::of(&Cell::new(&resident, &st)?)?;
        assert_eq!((shape.input_len, shape.words), (96, 11 * 35 + 3));
        assert_eq!(shape.witness_len(), 3_200);
        let bytes = shape.proof_len(max);
        assert_eq!(bytes, 86_832);
        let header = crate::custody_mesh::HeaderOpening {
            w0_leaf: [0; 32],
            cell_root: [0; 32],
            journal: Default::default(),
            proof: vec![0; bytes],
        };
        assert_eq!(
            bincode::serialized_size(&header)?,
            crate::custody_mesh::MAX_HEADER_WIRE
        );
        assert!(bytes + 65 + 3 * 32 <= 92_000);
        Ok(())
    }

    #[test]
    fn every_party_matches_scalar_polarization() -> Result<()> {
        for width in [1usize, 64, 103, 104, 240] {
            let blind = random_seed()?;
            let cell: Vec<u8> = (0..width).map(|i| (i * 37) as u8).collect();
            let w = width as u16;
            let ranges = if w > 2 {
                vec![(0, 1), (w / 2, w)]
            } else {
                vec![(0, w)]
            };
            let st = statement(&blind, &cell, ranges)?;
            let resident = Circuit::resident(width);
            kkw::tests::differential(&Cell::new(&resident, &st)?, &[&blind[..], &cell].concat())?;
        }
        // A frame ending mid-lane shifts every private byte.
        let outer = Circuit::private_cell_outer(&[3; 32], b"seat", 300)?;
        let blind = random_seed()?;
        let inner = random_seed()?;
        let st = Statement {
            cell_root: outer.root(&blind, &inner),
            ranges: vec![(3, 6)],
            projected_bytes: inner[3..6].to_vec(),
        };
        assert_ne!(outer.frame.len() % 8, 0);
        kkw::tests::differential(&Cell::new(&outer, &st)?, &[blind, inner].concat())?;
        Ok(())
    }

    #[test]
    fn authenticated_projection_and_adversarial_openings() -> Result<()> {
        let blind = random_seed()?;
        let mut cell = [0x61; 64];
        let canary = random_seed()?;
        cell[32..].copy_from_slice(&canary);
        let st = statement(&blind, &cell, vec![(1, 5), (18, 22)])?;
        let mut path = [0x54; 65];
        path[64] = 0x40;
        let siblings = [[1; 32], [2; 32], [3; 32]];
        let branch = Branch {
            path: &path,
            siblings: &siblings,
        };
        let world = branch.root(&st.cell_root)?;
        let binding = branch.binding(&world, &st.cell_root)?;
        let mut proof = branch.prove(&world, &blind, &cell, &st)?;
        branch.verify(&world, 64, &st.ranges, &st, &proof)?;
        assert!(proof.len() <= 86_832);
        assert!(proof.windows(32).all(|w| w != canary && w != blind));
        println!(
            "authenticated leaf proof {} bytes; neither private 32-byte string appeared",
            proof.len()
        );

        let resident = Circuit::resident(64);
        let c = Cell::new(&resident, &st)?;
        let shape = Shape::of(&c)?;
        let d: [u8; 32] = proof[64..96].try_into()?;
        let start = 96 + 80 * kkw::tests::challenge_frontier(&d);
        let opening = start + PARTIES.ilog2() as usize * 16;
        for (name, offset) in [
            ("GGM puncture", start),
            ("hidden party commitment", opening),
            ("masked round state", opening + 64 + shape.input_len),
            ("inverse chi hint", opening + 64 + shape.input_len + 25 * 8),
            ("committed online broadcasts", 96 + 16 + 32),
            ("nonce", opening + 32),
            (
                "preprocessing correction",
                opening + 64 + shape.witness_len(),
            ),
            ("offline seed", 96),
        ] {
            proof[offset] ^= 1;
            assert!(
                branch.verify(&world, 64, &st.ranges, &st, &proof).is_err(),
                "{name}"
            );
            proof[offset] ^= 1;
            println!("rejected {name}");
        }
        let other = [[1; 32], [4; 32], [3; 32]];
        let wrong = Branch {
            path: &path,
            siblings: &other,
        };
        assert!(wrong.verify(&world, 64, &st.ranges, &st, &proof).is_err());
        assert!(branch
            .verify(&world, 64, &[(0, 4), (18, 22)], &st, &proof)
            .is_err());
        let wrong_world = wrong.root(&st.cell_root)?;
        assert!(wrong
            .verify(&wrong_world, 64, &st.ranges, &st, &proof)
            .is_err());
        let mut answer = st.clone();
        answer.projected_bytes[0] ^= 1;
        assert!(branch
            .verify(&world, 64, &st.ranges, &answer, &proof)
            .is_err());
        assert!(branch
            .verify(&world, 64, &st.ranges, &st, &proof[..proof.len() - 1])
            .is_err());
        cell[63] ^= 1;
        let input = [&blind[..], &cell].concat();
        assert!(!kkw::satisfied(&c, &input)?);
        for k in [0, 14] {
            let forged = kkw::prove_cheating(&c, &input, &binding, k)?;
            assert!(branch.verify(&world, 64, &st.ranges, &st, &forged).is_err());
            println!("rejected changed hidden witness with {k} corrupted preprocessing instances");
        }
        println!("rejected sibling, policy, authenticated context transplant, answer, truncation, bypassed hidden-byte mutation");
        Ok(())
    }

    #[test]
    #[ignore = "serial wall-clock benchmark"]
    fn authenticated_release_gate() -> Result<()> {
        let blind = random_seed()?;
        let cell = [0x61; 64];
        let st = statement(&blind, &cell, vec![(1, 5), (18, 22)])?;
        let path = [0; 65];
        let siblings = [[1; 32], [2; 32], [3; 32]];
        let branch = Branch {
            path: &path,
            siblings: &siblings,
        };
        let world = branch.root(&st.cell_root)?;
        let branch_bytes = path.len() + std::mem::size_of_val(&siblings);
        println!(
            "workers={} public_branch_bytes={branch_bytes}",
            rayon::current_num_threads()
        );
        let mut samples = [vec![], vec![], vec![]];
        for _ in 0..9 {
            let t = Instant::now();
            let p = branch.prove(&world, &blind, &cell, &st)?;
            let prove_ms = t.elapsed().as_secs_f64() * 1000.;
            let t = Instant::now();
            branch.verify(&world, 64, &st.ranges, &st, &p)?;
            let verify_ms = t.elapsed().as_secs_f64() * 1000.;
            println!(
                "bytes={} prove_ms={prove_ms:.3} verify_ms={verify_ms:.3}",
                p.len()
            );
            assert!(p.len() + branch_bytes <= 92_000);
            for (v, x) in samples
                .iter_mut()
                .zip([p.len() as f64, prove_ms, verify_ms])
            {
                v.push(x);
            }
        }
        for v in &mut samples {
            v.sort_by(f64::total_cmp);
        }
        println!(
            "medians bytes={} prove_ms={:.3} verify_ms={:.3}",
            samples[0][4], samples[1][4], samples[2][4]
        );
        assert!(samples[1][4] <= 120., "prove median exceeded 120 ms");
        assert!(samples[2][4] <= 40., "verify median exceeded 40 ms");
        Ok(())
    }
}
