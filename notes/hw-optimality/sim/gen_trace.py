"""Synthetic Accel-Sim SASS trace (text .traceg, tracer version 5 layout) for issue-rate probes without NVBit.
Lane hw-opt-sim, 2026-11-06. Mirrors probe_sm75.cu k_rate: U independent accumulator chains per warp, operands
in registers, no memory traffic.  Usage:
    python3 gen_trace.py OUTDIR KIND BLOCKS THREADS ITERS BINARY_VERSION
KIND: u8 (IMMA.8816.U8.U8), u8_16832 / f16_16816 (sm_80+ mma.sync shapes), u4 (IMMA.8832.U4.U4), b1 (BMMA.88128.XOR.POPC), f16 (HMMA.1688.F32),
      lop3 (LOP3.LUT), hgmma256 / igmma256 (Hopper warpgroup MMA, N = 256; one per warp per step).
Writes OUTDIR/kernelslist.g and OUTDIR/kernel-1.traceg."""
import os, sys
out, kind, blocks, threads, iters, binver = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
U = 8
OPS = {"u8": "IMMA.8816.U8.U8", "u4": "IMMA.8832.U4.U4", "b1": "BMMA.88128.XOR.POPC", "f16": "HMMA.1688.F32",
       "lop3": "LOP3.LUT", "u8_16832": "IMMA.16832.U8.U8", "f16_16816": "HMMA.16816.F32", "hgmma256": "HGMMA.64x256x16.F32", "igmma256": "IGMMA.64x256x32.S8.S8"}
op = OPS[kind]
gmma = "GMMA" in op
def inst(pc, u):
    if kind == "lop3":
        d = 16 + u
        return f"{pc:04x} ffffffff 1 R{d} {op} 3 R{d} R2 R{16 + (u + 1) % U} 0"
    if gmma:   # dst = accumulator base, srcs = descriptors in UR regs + accumulator; commit flag 1 on the last of a step
        d = 32 + 8 * u
        return f"{pc:04x} ffffffff 1 R{d} {op} 3 UR4 UR6 R{d} {1 if u == U - 1 else 0} 0"
    d = 16 + 4 * u
    return f"{pc:04x} ffffffff 1 R{d} {op} 3 R2 R3 R{d} 0"
body = []
pc = 0x100
for it in range(iters):
    for u in range(U):
        body.append(inst(pc + 0x10 * u, u))
body.append(f"{pc + 0x10 * U:04x} ffffffff 0 EXIT 0 0")
os.makedirs(out, exist_ok=True)
with open(f"{out}/kernel-1.traceg", "w") as f:
    f.write(f"-kernel name = synth_{kind}\n-kernel id = 1\n-grid dim = ({blocks},1,1)\n-block dim = ({threads},1,1)\n"
            f"-shmem = 0\n-nregs = 96\n-binary version = {binver}\n-cuda stream id = 0\n"
            "-shmem base_addr = 0x00007f0000000000\n-local mem base_addr = 0x00007e0000000000\n"
            "-nvbit version = synthetic\n-accelsim tracer version = 5\n-enable lineinfo = 0\n\n"
            "#traces format = PC mask dest_num [reg_dests] opcode src_num [reg_srcs] mem_width [adrrescompress?] [mem_addresses]\n")
    for b in range(blocks):
        f.write(f"\n#BEGIN_TB\n\nthread block = {b},0,0\ncluster id = 0,0,0\ncluster cta = 0,0,0\ncluster rank = 0\n")
        for w in range(threads // 32):
            f.write(f"\nwarp = {w}\ninsts = {len(body)}\n" + "\n".join(body) + "\n")
        f.write("\n#END_TB\n")
with open(f"{out}/kernelslist.g", "w") as f:
    f.write("kernel-1.traceg\n")
print(kind, op, "blocks", blocks, "threads", threads, "insts/warp", len(body))
