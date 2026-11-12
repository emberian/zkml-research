#!/usr/bin/env python3
"""A short TCP probe of one link, both directions over connections the dialling side opens (so a seat that can only
dial is measured both ways): RTT (small-message round trips) and throughput with S parallel streams.

    tcpprobe.py serve PORT [--secs 600]          on the box that accepts (exits after --secs; start it with a PID file)
    tcpprobe.py dial HOST:PORT [--mb 512] [--streams 1,4] [--rtts 20]
Prints one JSON line: rtt_ms (min / median), up_mbit (dialler -> server) and down_mbit (server -> dialler) per stream count.
Throughput is timed at the receiver of the data: up from the first byte read to the last at the server (reported back),
down at the dialler."""
import json, socket, statistics, struct, sys, threading, time

def recv_exact(c, n):
    b = bytearray()
    while len(b) < n:
        x = c.recv(min(1 << 20, n - len(b)))
        if not x:
            raise EOFError
        b += x
    return bytes(b)

BUF = b"\0" * (1 << 20)

def send_n(c, n):
    while n > 0:
        k = min(n, len(BUF))
        c.sendall(BUF[:k]); n -= k

def drain(c, n):
    got, t0 = 0, None
    while got < n:
        x = c.recv(min(1 << 20, n - got))
        if not x:
            raise EOFError
        if t0 is None:
            t0 = time.time()
        got += len(x)
    return time.time() - t0

def handle(c):
    try:
        while True:
            op, n = struct.unpack("!cQ", recv_exact(c, 9))
            if op == b"p":
                c.sendall(b"p")
            elif op == b"u":      # dialler uploads n bytes; reply with the receive time
                c.sendall(struct.pack("!d", drain(c, n)))
            elif op == b"d":      # dialler downloads n bytes
                send_n(c, n)
            else:
                return
    except (EOFError, ConnectionError):
        pass
    finally:
        c.close()

def serve(port, secs):
    s = socket.socket(); s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("0.0.0.0", port)); s.listen(16); s.settimeout(5)
    end = time.time() + secs
    while time.time() < end:
        try:
            c, _ = s.accept()
        except socket.timeout:
            continue
        threading.Thread(target=handle, args=(c,), daemon=True).start()

def dial(hp, mb, streams, rtts):
    h, p = hp.rsplit(":", 1); p = int(p)
    c = socket.create_connection((h, p), timeout=60); c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    rt = []
    for _ in range(rtts):
        t = time.time(); c.sendall(struct.pack("!cQ", b"p", 0)); recv_exact(c, 1); rt.append(1000 * (time.time() - t))
    c.close()
    out = {"peer": hp, "rtt_ms_min": round(min(rt), 2), "rtt_ms_median": round(statistics.median(rt), 2), "mb": mb}
    for k in streams:
        n = mb * (1 << 20) // k
        for d in ("u", "d"):
            res = [None] * k
            def one(i):
                s = socket.create_connection((h, p), timeout=120)
                s.sendall(struct.pack("!cQ", d.encode(), n))
                if d == "u":
                    send_n(s, n); res[i] = struct.unpack("!d", recv_exact(s, 8))[0]
                else:
                    res[i] = drain(s, n)
                s.close()
            ts = [threading.Thread(target=one, args=(i,)) for i in range(k)]
            t0 = time.time(); [t.start() for t in ts]; [t.join() for t in ts]
            wall = time.time() - t0
            out[f"{'up' if d == 'u' else 'down'}_mbit_x{k}"] = round(8 * n * k / max(res) / 1e6, 1)
            out[f"{'up' if d == 'u' else 'down'}_wall_s_x{k}"] = round(wall, 2)
    print(json.dumps(out), flush=True)

if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k, d: a[a.index(k) + 1] if k in a else d
    if a[0] == "serve":
        serve(int(a[1]), float(opt("--secs", 600)))
    else:
        dial(a[1], int(opt("--mb", 512)), [int(x) for x in opt("--streams", "1,4").split(",")], int(opt("--rtts", 20)))
