"""
FCT-4: CLAASP's LINEAR_LAYER matrix convention -- evaluator vs model.

Found while building the mod-q emulation: an `addq` whose broadcast used a
LINEAR_LAYER passed an EXHAUSTIVE evaluator check, while reading the source
said the monomial-prediction model would compute the TRANSPOSE.

  evaluator, cipher_modules/generic_functions.py:106 `linear_layer`
      output[c] = XOR_r  input[r] AND matrix[r][c]        -> matrix[IN][OUT]
  MP model, .../Gurobi/monomial_prediction.py `add_linear_layer_constraints`
      output_vars[row] = sum over bits with matrix[row][bit]=1 -> matrix[OUT][IN]

Those are transposes.  They agree on symmetric matrices and disagree otherwise.
This decides it with an ASYMMETRIC matrix.

Guard: a SYMMETRIC matrix (where the two conventions must coincide) is run as a
control.  If the control also disagrees, the test is measuring something else.
"""
import sys
from claasp.cipher import Cipher
from claasp.cipher_modules.models.milp.milp_models.Gurobi.monomial_prediction \
    import MilpMonomialPredictionModel

N = 4


def build(matrix):
    c = Cipher("lltest", "permutation", ["input"], [N], N)
    c.add_round()
    c.add_linear_layer_component(["input"], [list(range(N))], N, matrix)
    c.add_cipher_output_component(["linear_layer_0_0"], [list(range(N))], N)
    return c


def anf_and_truth(matrix, label):
    c = build(matrix)
    milp = MilpMonomialPredictionModel(c)
    anf0 = milp.find_anf_of_specific_output_bit(0)          # bit 0 = MSB
    # ground truth from the evaluator, for the SAME bit
    ev = {}
    for x in range(1 << N):
        ev[x] = (c.evaluate([x]) >> (N - 1)) & 1
    # which single-input-bit XOR pattern does the evaluator realise?
    terms = [i for i in range(N)
             if ev[1 << (N - 1 - i)] != ev[0]]
    ok = MilpMonomialPredictionModel(build(matrix)).check_anf_correctness(0, num_tests=200)
    print(f"  {label}")
    print(f"    MP model ANF of output bit 0 : {anf0}")
    print(f"    evaluator realises           : {' + '.join('i%d' % i for i in terms) or '0'}")
    print(f"    check_anf_correctness(200)   : {ok}")
    return str(anf0), terms, ok


print("=" * 78)
print("FCT-4  LINEAR_LAYER: does the evaluator agree with the model?")
print("=" * 78)

# CONTROL: symmetric matrix -- the two conventions coincide, so they MUST agree.
sym = [[1, 1, 0, 0],
       [1, 1, 0, 0],
       [0, 0, 1, 0],
       [0, 0, 0, 1]]
print("\nCONTROL (symmetric matrix -- transpose is a no-op, must AGREE):")
_, _, ok_sym = anf_and_truth(sym, "M = M^T")

# THE TEST: asymmetric.
asym = [[1, 1, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1]]
print("\nTEST (asymmetric matrix -- the conventions differ):")
anf, terms, ok_asym = anf_and_truth(asym, "M != M^T")

print()
print("=" * 78)
if not ok_sym:
    print("CONTROL FAILED: even a symmetric matrix disagrees.  Something else is")
    print("wrong; this test cannot testify about the transpose.  NO VERDICT.")
    sys.exit(2)
print("control passes: on a symmetric matrix evaluator and model agree.")
print()
if not ok_asym:
    print("VERDICT: on an ASYMMETRIC linear layer the CLAASP-MP model and the")
    print("  CLAASP evaluator compute TRANSPOSED maps.  `check_anf_correctness`")
    print("  detects it, but only if the user runs it; neither layer refuses.")
    print()
    print(f"  model says output bit 0 = {anf}")
    print(f"  evaluator says output bit 0 = "
          f"{' + '.join('i%d' % i for i in terms) or '0'}")
else:
    print("VERDICT: they agree even on an asymmetric matrix -- the source reading")
    print("  that motivated this test was wrong.  Do not repeat the claim.")
