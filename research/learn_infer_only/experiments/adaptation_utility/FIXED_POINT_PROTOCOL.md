# Follow-on fixed-point readout protocol (written after v1, before these results)

[DERIVED specification] New held-out history seeds 44000..44031 use the same v1
coordinate split and concept family. Hyperparameters stay frozen from v1 selection.
Compare floating LMS against bounded integer LMS for the 577-, 65-, and 6-scalar
readouts at Q=2^8,2^12,2^16; report every scale, with no best-scale selection. This is
an exact readout arithmetic experiment, not a replacement theorem for float32
transformer feature extraction and not encrypted execution.

[DERIVED specification] A fixed importer maps feature v to clip(round_even(Q*v),
-Q,Q). This importer is executed with NumPy float64. Its feature/output arrays and
hashes are retained; the integer transition thereafter contains no floating arithmetic.
Integer state M starts zero and is always clipped to [-16Q,16Q]. R=round_even(rho Q).
For a teaching label y in {-1,+1}, compute D=sum_i M_i P_i;
s= floor((D+Q/2)/Q), e=Q*y-s; then
M'_i = clip(floor((R*M_i + e*P_i+Q/2)/Q), -16Q,16Q).
All selected v1 step sizes equal 1; this follow-on refuses any other eta.
Infer returns +1 iff sum_i M_i P_i >=0. Python/NumPy integer arithmetic uses
signed int64; the contract supplies a conservative universal no-overflow bound.

[DERIVED] If |M_i|<=16Q, |P_i|<=Q, 0<=R<=Q and dimension r,
|D|<=16rQ², |s|<=16rQ+1, |e|<=(16r+1)Q+1.
Thus each unrounded update numerator including Q/2 has absolute value at most
(16r+17)Q² + 3Q/2. For r<=577,Q<=65536, these integer bounds are below 2^63.
The max of observed numerators is supplementary evidence, not the universal bound.
Saturation and floor rounding are private nonlinear operations if state is encrypted.

[DERIVED specification] Record class agreement with floating LMS, independent
accuracy, before/post-change scores, clipping counts, max absolute integer state,
max intermediate magnitude, and executed reset/swap controls. Bit-exact agreement
of int64 vectorized transition and a separate Python-bigint reference is tested on
random states, extremal states, every scale, and positive/negative rounding ties.
Changing the numerical contract can change utility; no approximation freedom is
granted to a prover by this experiment.
