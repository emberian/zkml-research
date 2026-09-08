#!/usr/bin/env python3
"""Preview only the generated public directory, under the Pages project path."""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlsplit

DIST = Path(__file__).resolve().parent / "dist"
BASE = "/zkml-research/"


class Handler(SimpleHTTPRequestHandler):
    def do_GET(self):
        if urlsplit(self.path).path == BASE[:-1]:
            self.send_response(308)
            self.send_header("Location", BASE)
            self.end_headers()
            return
        if not urlsplit(self.path).path.startswith(BASE):
            self.send_error(404)
            return
        super().do_GET()

    def translate_path(self, path):
        relative = unquote(urlsplit(path).path[len(BASE):])
        candidate = (DIST / relative).resolve()
        if not candidate.is_relative_to(DIST) or any(part.startswith(".") for part in Path(relative).parts):
            return str(DIST / "__not_public__")
        return str(candidate)

    def list_directory(self, path):
        self.send_error(404)
        return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=4173)
    args = parser.parse_args()
    if not (DIST / "index.html").is_file():
        parser.error("Run python3 website/build.py first")
    server = ThreadingHTTPServer(("127.0.0.1", args.port), partial(Handler, directory=str(DIST)))
    print(f"Preview: http://127.0.0.1:{args.port}{BASE}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        server.server_close()
