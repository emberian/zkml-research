//! Research backend: two whole-row MAC equations over the exact BFV RNS field.
//! All 16 columns are public, recomputed preprocessing. There is no private witness.
use crate::field::{BfvField, BfvParameters};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{HashChallenger, SerializingChallenger64};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::{PrimeCharacteristicRing, extension::BinomialExtensionField};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CompressionFunctionFromHasher, CryptographicHasher, SerializingHasher};
use p3_uni_stark::{
    Proof, StarkConfig, prove_with_preprocessed, setup_preprocessed, verify_with_preprocessed,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::time::Instant;

pub const ROWS: usize = 1024;
pub const WIDTH: usize = 16;
pub const PROFILE: &str = "matched-bfv-public-mac-v1|p3-82cfad73-local-fri-challenger|sha256-domains-v1|rows1024|lb3|lfp0|arity3|q64|pow0|ext4|nonhiding";

/// Standard SHA-256 with disjoint prefix domains for leaves, parents and FS.
#[derive(Copy, Clone, Debug)]
pub struct DomainHash(&'static [u8]);
impl CryptographicHasher<u8, [u8; 32]> for DomainHash {
    fn hash_iter<I: IntoIterator<Item = u8>>(&self, input: I) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update((self.0.len() as u64).to_le_bytes());
        h.update(self.0);
        let mut block = [0u8; 512];
        let mut used = 0;
        for byte in input {
            block[used] = byte;
            used += 1;
            if used == block.len() {
                h.update(block);
                used = 0;
            }
        }
        h.update(&block[..used]);
        h.finalize().into()
    }
}

type Challenge<const Q: u64> = BinomialExtensionField<BfvField<Q>, 4>;
type Challenger<const Q: u64> =
    SerializingChallenger64<BfvField<Q>, HashChallenger<u8, DomainHash, 32>>;
type Compress = CompressionFunctionFromHasher<DomainHash, 2, 32>;
type Mmcs<const Q: u64> =
    MerkleTreeMmcs<BfvField<Q>, u8, SerializingHasher<DomainHash>, Compress, 2, 32>;
type Pcs<const Q: u64> = TwoAdicFriPcs<
    BfvField<Q>,
    Radix2DitParallel<BfvField<Q>>,
    Mmcs<Q>,
    ExtensionMmcs<BfvField<Q>, Challenge<Q>, Mmcs<Q>>,
>;
type Config<const Q: u64> = StarkConfig<Pcs<Q>, Challenge<Q>, Challenger<Q>>;

fn config<const Q: u64>(context: &[u8; 32]) -> Config<Q>
where
    BfvField<Q>: BfvParameters,
{
    let mmcs = Mmcs::new(
        SerializingHasher::new(DomainHash(b"vfhe-matched-leaf-v1")),
        Compress::new(DomainHash(b"vfhe-matched-node-v1")),
        0,
    );
    let fri = FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries: 64,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ExtensionMmcs::new(mmcs.clone()),
    };
    let pcs = Pcs::new(Radix2DitParallel::default(), mmcs, fri);
    let mut initial = PROFILE.as_bytes().to_vec();
    initial.extend_from_slice(&Q.to_le_bytes());
    initial.extend_from_slice(context);
    // Upstream masks ceil(log2 Q) byte-stream bits and rejects values >= Q.
    // No integer-mod-Q sampling is used for transcript challenges.
    Config::new(
        pcs,
        Challenger::from_hasher(initial, DomainHash(b"vfhe-matched-transcript-v1")),
    )
}

pub struct MacAir<const Q: u64>
where
    BfvField<Q>: BfvParameters,
{
    public: RowMajorMatrix<BfvField<Q>>,
}
impl<const Q: u64> MacAir<Q>
where
    BfvField<Q>: BfvParameters,
{
    pub fn new(rows: &[[u64; 16]]) -> Result<Self, String> {
        if rows.len() != ROWS {
            return Err(format!("expected {ROWS} whole rows"));
        }
        if rows.iter().flatten().any(|x| *x >= Q) {
            return Err("noncanonical residue".into());
        }
        Ok(Self {
            public: RowMajorMatrix::new(
                rows.iter()
                    .flatten()
                    .map(|x| BfvField::<Q>::from_u64(*x))
                    .collect(),
                WIDTH,
            ),
        })
    }
}
impl<const Q: u64> BaseAir<BfvField<Q>> for MacAir<Q>
where
    BfvField<Q>: BfvParameters,
{
    fn width(&self) -> usize {
        1
    }
    fn preprocessed_width(&self) -> usize {
        WIDTH
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<BfvField<Q>>> {
        Some(self.public.clone())
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn num_constraints(&self) -> Option<usize> {
        Some(3)
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}
impl<const Q: u64, AB: AirBuilder<F = BfvField<Q>>> Air<AB> for MacAir<Q>
where
    BfvField<Q>: BfvParameters,
{
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        b.assert_zero(main.current(0).unwrap());
        let pre: [AB::Var; 16] = core::array::from_fn(|j| b.preprocessed().current(j).unwrap());
        for component in 0..2 {
            let mut total: AB::Expr = pre[12 + component].into();
            for j in 0..4 {
                total += pre[j] * pre[4 + 4 * component + j];
            }
            // Deliberately no transition/first/last-row selector: both equations
            // are asserted on every row, including row 1023.
            b.assert_eq(total, pre[14 + component]);
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Timing {
    pub preprocessing_ns: u128,
    pub proof_ns: u128,
    pub verify_ns: u128,
    pub proof_bytes: usize,
}

pub fn prove_chunk<const Q: u64>(
    rows: &[[u64; 16]],
    context: &[u8; 32],
) -> Result<(Vec<u8>, Timing), String>
where
    BfvField<Q>: BfvParameters,
{
    check_rows(Q, rows)?;
    let air = MacAir::<Q>::new(rows)?;
    let cfg = config::<Q>(context);
    let t = Instant::now();
    let (prep, vk) = setup_preprocessed(&cfg, &air, 10).ok_or("missing public preprocessing")?;
    let preprocessing_ns = t.elapsed().as_nanos();
    let t = Instant::now();
    let proof = prove_with_preprocessed(
        &cfg,
        &air,
        RowMajorMatrix::new(vec![BfvField::<Q>::ZERO; ROWS], 1),
        &[],
        Some(&prep),
    );
    let proof_ns = t.elapsed().as_nanos();
    let t = Instant::now();
    verify_with_preprocessed(&cfg, &air, &proof, &[], Some(&vk))
        .map_err(|e| format!("self verification: {e:?}"))?;
    let verify_ns = t.elapsed().as_nanos();
    let bytes = postcard::to_allocvec(&proof).map_err(|e| e.to_string())?;
    let timing = Timing {
        preprocessing_ns,
        proof_ns,
        verify_ns,
        proof_bytes: bytes.len(),
    };
    Ok((bytes, timing))
}

pub fn verify_chunk<const Q: u64>(
    rows: &[[u64; 16]],
    context: &[u8; 32],
    bytes: &[u8],
) -> Result<Timing, String>
where
    BfvField<Q>: BfvParameters,
{
    if bytes.len() > 8 << 20 {
        return Err("proof byte cap exceeded".into());
    }
    let air = MacAir::<Q>::new(rows)?;
    let cfg = config::<Q>(context);
    let (proof, tail): (Proof<Config<Q>>, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|e| e.to_string())?;
    if !tail.is_empty() {
        return Err("trailing proof bytes".into());
    }
    if postcard::to_allocvec(&proof).map_err(|e| e.to_string())? != bytes {
        return Err("noncanonical proof encoding".into());
    }
    if proof.degree_bits != 10 {
        return Err("proof degree differs from fixed 1024 rows".into());
    }
    let t = Instant::now();
    // The consumer computes this commitment itself. No producer-supplied VK,
    // root, exported row file, or self-verification flag is trusted.
    let (_, vk) = setup_preprocessed(&cfg, &air, 10).ok_or("missing public preprocessing")?;
    let preprocessing_ns = t.elapsed().as_nanos();
    let t = Instant::now();
    verify_with_preprocessed(&cfg, &air, &proof, &[], Some(&vk))
        .map_err(|e| format!("verification: {e:?}"))?;
    Ok(Timing {
        preprocessing_ns,
        proof_ns: 0,
        verify_ns: t.elapsed().as_nanos(),
        proof_bytes: bytes.len(),
    })
}

/// Direct arithmetic comparator, not used as a substitute for proof consumption.
pub fn check_rows(q: u64, rows: &[[u64; 16]]) -> Result<(), String> {
    for (i, r) in rows.iter().enumerate() {
        if r.iter().any(|x| *x >= q) {
            return Err(format!("noncanonical row {i}"));
        }
        for c in 0..2 {
            let mut sum = r[12 + c] as u128;
            for j in 0..4 {
                sum += r[j] as u128 * r[4 + 4 * c + j] as u128;
            }
            if (sum % q as u128) as u64 != r[14 + c] {
                return Err(format!("MAC failed at row {i}, component {c}"));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    const Q: u64 = 1125899906826241;
    fn fixture() -> Vec<[u64; 16]> {
        (0..ROWS)
            .map(|i| {
                let mut r =
                    core::array::from_fn(|j| (i as u64 * 1777 + j as u64 * 7919 + Q - 4000) % Q);
                for c in 0..2 {
                    let mut v = r[12 + c] as u128;
                    for j in 0..4 {
                        v += r[j] as u128 * r[4 + 4 * c + j] as u128;
                    }
                    r[14 + c] = (v % Q as u128) as u64;
                }
                r
            })
            .collect()
    }
    #[test]
    fn whole_row_air_accepts_and_rejects_last_row_both_components() {
        let rows = fixture();
        let trace = RowMajorMatrix::new(vec![BfvField::<Q>::ZERO; ROWS], 1);
        p3_air::check_constraints(&MacAir::<Q>::new(&rows).unwrap(), &trace, &[]);
        for column in [14, 15] {
            let mut bad = rows.clone();
            bad[ROWS - 1][column] = (bad[ROWS - 1][column] + 1) % Q;
            assert!(
                std::panic::catch_unwind(|| p3_air::check_constraints(
                    &MacAir::<Q>::new(&bad).unwrap(),
                    &trace,
                    &[]
                ))
                .is_err()
            );
        }
    }
    #[test]
    fn residues_shapes_and_domains_are_exact() {
        let mut rows = fixture();
        rows[0][0] = Q;
        assert!(MacAir::<Q>::new(&rows).is_err());
        assert!(MacAir::<Q>::new(&rows[..ROWS - 1]).is_err());
        let data = [1u8; 64];
        assert_ne!(
            DomainHash(b"vfhe-matched-leaf-v1").hash_iter(data),
            DomainHash(b"vfhe-matched-node-v1").hash_iter(data)
        );
    }
    #[test]
    #[ignore = "requires coordinated native proof slot"]
    fn full_profile_proof_rejects_wrong_context_changed_row_and_trailing_bytes() {
        let rows = fixture();
        let context = [7u8; 32];
        let (bytes, _) = prove_chunk::<Q>(&rows, &context).unwrap();
        verify_chunk::<Q>(&rows, &context, &bytes).unwrap();
        assert!(verify_chunk::<Q>(&rows, &[8u8; 32], &bytes).is_err());
        let mut bad = rows.clone();
        bad[ROWS - 1][15] = (bad[ROWS - 1][15] + 1) % Q;
        assert!(verify_chunk::<Q>(&bad, &context, &bytes).is_err());
        let mut extra = bytes;
        extra.push(0);
        assert!(verify_chunk::<Q>(&rows, &context, &extra).is_err());
    }
}
