# Predeclared bounded repair grid

[DERIVED/EXECUTED declaration, 2026-09-08] Declared after the 24 baseline
calls and before any repair-grid outputs. Maximum40 additional estimator
calls; no cryptographic or lattice-attack execution.

1. Twenty-four grid calls: n∈{8192,16384,20480,24576}, l=262144,
   σe=1024, q_low=the first proven prime above2^292; attacks
   {dual,uSVP,BDD}; models {MATZOV classical,ADPS16 quantum core-SVP}.
   These dimensions all satisfy the general Gaussian regularity entropy
   check with σK=2^32 and q<2^293. Set flood F=2^248, four bits above
   the baseline, compensating exactly for the sixteenfold height increase.
2. Twelve validation calls on the smallest grid dimension whose completed
   grid costs all exceed128 in each named model: both endpoint-adjacent
   proven primes q_low>2^292 and q_high<2^293; attacks{dual,uSVP,BDD};
   models{ADPS16 classical,MATZOV quantum depth×width}. If no grid point
   qualifies, do not spend these calls on an undeclared adaptive grid.
3. Four baseline low-endpoint explicit beta2 dual calls, one per original
   model, to expose the optimizer's beta40 floor and cost-model behavior.
   Error/status remains recorded if a model does not support beta2.

[DERIVED] The target128 means a named heuristic modeled cost threshold,
separately for classical and quantum models. It is not certified security
and does not account for the theorem's factor768. The selected point must
also be priced and its finite correctness/statistical inequalities checked;
grid dimensions alone are not an implementation proposal.

[OPEN] HYL's general-function source prescription is compared analytically:
increasing l′ to meet its actual≥2nlogq premise also raises Gaussian/noise
and smudging costs. No source table will be fed to an estimator as if its
uncertified finite reduction constants had been resolved.
