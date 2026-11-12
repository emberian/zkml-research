#!/usr/bin/env python3
"""sendonce.py FILE PORT [SECS]: serve FILE to the first client that connects to 0.0.0.0:PORT, then exit (or after SECS,
default 900). For moving public build artifacts box to box when the receiver can only dial; the receiver checks sha256."""
import socket, sys
f, port = sys.argv[1], int(sys.argv[2])
s = socket.socket(); s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("0.0.0.0", port)); s.listen(1); s.settimeout(float(sys.argv[3]) if len(sys.argv) > 3 else 900)
c, peer = s.accept()
with open(f, "rb") as fh:
    c.sendfile(fh)
c.close()
print("sent to", peer[0])
