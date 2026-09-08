# Fusing ring evaluation and the ring-switch quotient witness

[SOURCE starting point] `tremblaythibaultl/matvecmul` at local commit `00379074cad457367a86dde2ecee9d0f318a7e12`, `src/protocol/prover/mod.rs:96–107`, computes the full polynomial matrix-vector product and divides by `X^N+1`. Lines 153–155 independently recompute the ring matrix-vector product, although the previously computed remainders are available. `PolynomialRing` pads to `2N` coefficients; the common NTT multiplication backend transforms each pair afresh. The paper is *Practical SNARGs for Matrix Multiplications over Encrypted Data*, eprint 2026/027, §3.2/Algorithm 3, read from the local mirror. Its quotient commitment is sent before the polynomial-evaluation challenge.

[DERIVED exact relation] Let `F` be an odd-characteristic field, `N` a power of two, and all entries of public matrix `A` and input component matrix `C` have degree below `N`. For output row `i` and component `k`, define

`S_ik(X) = Σ_j A_ij(X) C_jk(X)`.

There are unique `Y_ik,Q_ik` satisfying

`S_ik = Y_ik + (X^N+1) Q_ik`, `deg Y_ik < N`, `deg Q_ik ≤ N−2`.

Write `S=L+X^N H`, with both blocks padded to `N` coefficients. Then `Y=L−H` and `Q=H`. At `N=1`, `H=0`, so the quotient is zero. This is an ordinary polynomial identity, not a relation checked only at NTT roots. It is exactly the ring-switch witness required by the paper.

[DERIVED executable delta A] Precompute each public matrix entry's transform of length `2N`. Transform each input component once, reuse it across output rows, accumulate all Hadamard products at each frequency, and inverse-transform once per output component. Split the resulting two coefficient blocks into `Y,Q`. This shares the real arithmetic between evaluation and witness generation and eliminates a separate ring multiplication. The prototype uses a cyclic `2N` transform; zero padding makes the product degree `<2N`, so no cyclic wrap occurs. The author's current backend instead uses a negacyclic `2N` transform, also exact on these zero-padded inputs.

[DERIVED executable delta B] When a genuine N-point negacyclic FHE transform is already the runtime interface, retain it and add its complementary cyclic N-point transform. Compute

`Y = S mod(X^N+1) = L−H`, `D = S mod(X^N−1) = L+H`.

Since `2` is invertible, **`Q=(D−Y)/2`**. Cache both public-matrix transforms; transform each input once per coset; accumulate products before the two inverse transforms. This uses only a primitive `2N`-th root, preserves the existing N-point FHE domain, and supplies the quotient without an independent full-product pass. The two quotient rings are comaximal because their defining polynomials differ by `2`; no statement of this form is claimed in characteristic two.

[DERIVED costs] For `r` output rows, inner dimension `m`, and `k` components, the per-product duplicate pattern makes `3rmk` transforms at length `2N` and `3rmk` at length `N`. Delta A uses `rm` public preprocessing transforms and `mk+rk` online transforms at length `2N`. Delta B uses `2rm` public preprocessing transforms and `2mk+2rk` online transforms at length `N`. Delta A and B both use `2Nrmk` pointwise products; the duplicate pattern uses `3Nrmk`. Cache construction, inverse normalization, twists, linear recombination and coefficient accumulation remain real costs and are measured separately. These are algebraic operation counts, not a prediction of Rust/HE/proof wall time.

[DERIVED proof interface] After `A,C,Y,Q` are bound by the actual commitment/transcript scheme and before sampling `α`, the relation becomes `Σ_j A_ij(α)C_jk(α)−Y_ik(α)−(α^N+1)Q_ik(α)=0`. A nonzero residual has degree at most `2N−2`; a uniform independent extension-field challenge misses it with probability at most `(2N−2)/|E|`. Row/component batching and PCS opening soundness add their own terms. The prototype checks exact identities; it does not instantiate this verifier or make a Fiat–Shamir/ROM/QROM claim. Full coordinate order, root, twist convention and modulus must belong to the emitted relation/cache identity.

[DERIVED handoff] At fixed `α` and fixed outer MLE challenge, reuse one powers-of-`α` vector and one row/component equality-weight table for both `Y` and `Q`. This is the immediate connection to polynomial_gluing's streamed MLE binding. No new PCS, transcript order or FHE security parameter is needed to define this arithmetic replacement.

[DERIVED degree accounting] The honest generator asserts the top quotient coefficient is zero. To claim the tighter `2N−2` residual bound in a verifier game, that quotient-degree restriction must also be enforced on adversarial commitments. A commitment to an unrestricted length-N quotient table instead permits degree `2N−1` in the residual; the paper's conservative `2N/|E|` bound still covers it. The native integration preserves the verifier and does not claim a tighter protocol soundness constant merely from the honest generator assertion.

[OPEN scope] This is a concrete algorithmic delta against the named implementation and old scalar demonstration relation, not a claim of a new cryptographic construction or a new CRT theorem. Integration into a real emitted NTT/vector relation, cryptographic proof generation, native performance and FHE parameter security are separate work. The small public prototype creates no keys or ciphertext secrets and changes no companion source.
