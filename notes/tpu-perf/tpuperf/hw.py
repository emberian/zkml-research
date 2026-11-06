"""Hardware numbers per TPU generation, each with its provenance tag.

[READ:sb]  jax-ml.github.io/scaling-book/tpus (spec table, read 2026-11-06)
[READ:cc]  the TPU compiler itself, deviceless on hbox (GROUNDING section 0)
[INFERRED] derived from READ numbers; the derivation is in the comment
[MEASURE]  not published; a calibration microbenchmark on the device fills it (profile.py --calibrate)

Rates are per chip, in operations per second (a multiply-add is 2 operations).
"""
GEN = {
    "v5e": dict(
        topology="v5e:1x1", kaggle="TpuV5E8",
        bf16=1.97e14,            # [READ:sb]
        int8=3.94e14,            # [READ:sb]
        hbm_bw=8.2e11,           # [READ:sb] bytes/s
        hbm_bytes=16 * 2**30,    # [READ:sb]
        vmem_bytes=128 * 2**20,  # [READ:cc] RESOURCE_EXHAUSTED message: "would exceed memory (size=134217728)" space=vmem
        mxu=(128, 128), n_mxu=4, # [READ:sb] 128x128 before v6e, 4 MXUs on v4/v5
        clock_hz=1.50e9,         # [INFERRED] 1.97e14 / (4 MXU * 128*128 MAC * 2)
        # VPU: (8,128) lanes [READ:sb]; per-cycle ALU count for v5e is not published (sb gives 4 ALUs/lane on TPU7x).
        # Placeholder 8*128*4*clock = 6.1e12 32-bit ops/s [INFERRED, unverified]; calibration replaces it.
        vpu_ops=8 * 128 * 4 * 1.50e9,
        vpu_src="INFERRED-unverified",
    ),
    "v6e": dict(
        topology="v6e:1x1", kaggle=None,
        bf16=9.20e14, int8=1.84e15, hbm_bw=1.6e12, hbm_bytes=32 * 2**30,  # [READ:sb]
        vmem_bytes=128 * 2**20,  # [READ:cc] same RESOURCE_EXHAUSTED probe on the v6e topology
        mxu=(256, 256), n_mxu=2, # [READ:sb] "256x256 systolic array"; "2 for TPU v3, TPU v6e, and TPU7x"
        clock_hz=9.20e14 / (2 * 256 * 256 * 2),  # [INFERRED] = 3.5e9: implausible, so n_mxu or the rate reading is off;
                                                 # used only to convert compiler cycle estimates, flagged in reports
        vpu_ops=None, vpu_src="unknown (no v6e on Kaggle)",
    ),
}


def peak(gen, unit):
    g = GEN[gen]
    return {"mxu_int8": g["int8"], "mxu_bf16": g["bf16"], "hbm": g["hbm_bw"], "vpu": g["vpu_ops"]}[unit]
