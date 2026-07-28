#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse


FRONTEND = Path(__file__).resolve().parent
ROOT = FRONTEND.parent
ASSETS = {
    "/": ("index.html", "text/html; charset=utf-8"),
    "/app.js": ("app.js", "text/javascript; charset=utf-8"),
    "/style.css": ("style.css", "text/css; charset=utf-8"),
}


def default_binary() -> Path:
    candidates = (
        ROOT / "leanreach.exe",
        ROOT / ".lake/build/leanreach-dist/leanreach.exe",
        ROOT / ".lake/build/bin/leanreach.exe",
        ROOT / ".lake/build/bin/leanreach",
    )
    return next((path for path in candidates if path.exists()), candidates[1])


class Worker:
    def __init__(self, command: list[str], cwd: Path):
        self.command = command
        self.cwd = cwd
        self.lock = threading.Lock()
        self.process: subprocess.Popen[str] | None = None

    def start(self) -> None:
        self.close()
        self.process = subprocess.Popen(
            self.command,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,
        )
        self._exchange("search __leanreach_frontend_ready__")

    def close(self) -> None:
        if self.process is None:
            return
        if self.process.poll() is None:
            assert self.process.stdin
            try:
                self.process.stdin.write("\n")
                self.process.stdin.flush()
                self.process.wait(timeout=2)
            except (BrokenPipeError, subprocess.TimeoutExpired):
                self.process.kill()
                self.process.wait()
        self.process = None

    def _exchange(self, command: str) -> dict:
        assert self.process and self.process.stdin and self.process.stdout
        self.process.stdin.write(command + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError("LeanReach worker stopped")
        return json.loads(line)

    def query(self, command: str) -> dict:
        with self.lock:
            for attempt in range(2):
                try:
                    if self.process is None or self.process.poll() is not None:
                        self.start()
                    return self._exchange(command)
                except (BrokenPipeError, json.JSONDecodeError, RuntimeError):
                    self.close()
                    if attempt:
                        raise
        raise RuntimeError("LeanReach worker did not respond")


class Server(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, address: tuple[str, int], worker: Worker):
        super().__init__(address, Handler)
        self.worker = worker


class Handler(BaseHTTPRequestHandler):
    server: Server

    def respond(self, status: int, content_type: str, body: bytes) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def json(self, status: int, value: dict) -> None:
        self.respond(
            status,
            "application/json; charset=utf-8",
            json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode(),
        )

    def do_GET(self) -> None:
        url = urlparse(self.path)
        if asset := ASSETS.get(url.path):
            name, content_type = asset
            self.respond(200, content_type, (FRONTEND / name).read_bytes())
            return
        if url.path != "/json":
            self.respond(404, "text/plain; charset=utf-8", b"Not found\n")
            return
        params = parse_qs(url.query)
        if query := params.get("q", [None])[0]:
            command = "search " + " ".join(query.split())
        elif name := params.get("name", [None])[0]:
            command = " ".join(name.split())
        else:
            self.json(400, {"error": "expected one 'q' or 'name' parameter"})
            return
        if len(command) > 512:
            self.json(400, {"error": "query is too long"})
            return
        try:
            self.json(200, self.server.worker.query(command))
        except Exception as error:
            self.json(503, {"error": str(error)})


def main() -> None:
    parser = argparse.ArgumentParser(description="LeanReach HTTP frontend")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8088)
    parser.add_argument("--leanreach-bin", type=Path, default=default_binary())
    parser.add_argument("--project-dir", type=Path, default=Path.cwd())
    args, extra = parser.parse_known_args()
    if extra[:1] == ["--"]:
        extra = extra[1:]
    binary = args.leanreach_bin.resolve()
    worker = Worker(
        [str(binary), "--interactive", "--json", *extra],
        args.project_dir.resolve(),
    )
    server = Server((args.host, args.port), worker)
    print(f"LeanReach frontend: http://{args.host}:{args.port}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
        worker.close()


if __name__ == "__main__":
    main()
