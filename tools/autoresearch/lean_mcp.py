"""Lightweight MCP client for lean-lsp-mcp.

Spawns lean-lsp-mcp as a subprocess, speaks MCP protocol (NDJSON over stdio),
and exposes tool calls as plain Python functions.

Usage:
    with LeanMCP("/path/to/lean4/project") as lsp:
        result = lsp.call("lean_diagnostic_messages", file_path="Omega/Core/Fib.lean")
        result = lsp.call("lean_multi_attempt", file_path="...", line=10, snippets=["simp", "ring"])
        result = lsp.call("lean_local_search", query="fiberCard")
"""

from __future__ import annotations

import json
import os
import select
import subprocess
import time
from pathlib import Path


class LeanMCP:
    def __init__(self, lean_project_path: str | Path):
        self.project_path = str(Path(lean_project_path).resolve())
        self.proc: subprocess.Popen | None = None
        self._next_id = 1
        self._buf = b""

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, *args):
        self.stop()

    def start(self):
        env = os.environ.copy()
        env["LEAN_PROJECT_PATH"] = self.project_path
        self.proc = subprocess.Popen(
            ["uvx", "lean-lsp-mcp"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            env=env,
        )
        resp = self._request("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "omega-autoresearch", "version": "1.0"},
        })
        if not resp or "result" not in resp:
            self.stop()
            raise RuntimeError("lean-lsp-mcp failed to initialize")
        self._notify("notifications/initialized")
        time.sleep(1)  # Let LSP warm up
        return self

    def stop(self):
        if self.proc:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=5)
            except Exception:
                self.proc.kill()
            self.proc = None

    def call(self, tool_name: str, timeout: float = 60.0, **kwargs) -> dict:
        """Call an MCP tool and return the result."""
        resp = self._request("tools/call", {
            "name": tool_name,
            "arguments": kwargs,
        }, timeout=timeout)
        if not resp:
            return {"error": "no response", "text": "", "isError": True}
        if "error" in resp:
            return {"error": resp["error"], "text": str(resp["error"]), "isError": True}
        result = resp.get("result", {})
        if isinstance(result, dict) and "content" in result:
            texts = []
            for block in result["content"]:
                if isinstance(block, dict) and block.get("type") == "text":
                    texts.append(block["text"])
            return {"text": "\n".join(texts), "isError": result.get("isError", False)}
        return result

    def list_tools(self) -> list[dict]:
        resp = self._request("tools/list", {})
        return resp.get("result", {}).get("tools", []) if resp else []

    # --- NDJSON MCP protocol ---

    def _request(self, method: str, params: dict, timeout: float = 30.0) -> dict | None:
        msg_id = self._next_id
        self._next_id += 1
        msg = {"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params}
        self._send(msg)
        return self._recv(msg_id, timeout)

    def _notify(self, method: str, params: dict | None = None):
        msg = {"jsonrpc": "2.0", "method": method}
        if params:
            msg["params"] = params
        self._send(msg)

    def _send(self, msg: dict):
        if not self.proc or not self.proc.stdin:
            raise RuntimeError("MCP process not running")
        line = json.dumps(msg) + "\n"
        os.write(self.proc.stdin.fileno(), line.encode())

    def _recv(self, expected_id: int, timeout: float = 30.0) -> dict | None:
        if not self.proc or not self.proc.stdout:
            return None
        deadline = time.time() + timeout
        while time.time() < deadline:
            remaining = deadline - time.time()
            ready, _, _ = select.select([self.proc.stdout], [], [], min(remaining, 0.5))
            if ready:
                chunk = os.read(self.proc.stdout.fileno(), 65536)
                if not chunk:
                    return None
                self._buf += chunk
            # Try to parse complete lines
            while b"\n" in self._buf:
                line, self._buf = self._buf.split(b"\n", 1)
                line = line.strip()
                if not line:
                    continue
                try:
                    data = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if data.get("id") == expected_id:
                    return data
        return None


# --- Convenience functions for autoresearch ---

def quick_check(lsp: LeanMCP, file_path: str) -> tuple[bool, str]:
    """Check a file for errors using lean_diagnostic_messages. Returns (ok, errors)."""
    result = lsp.call("lean_diagnostic_messages", file_path=file_path)
    text = result.get("text", "")
    has_error = result.get("isError", False) or "error" in text.lower()
    return (not has_error, text)


def search_lemmas(lsp: LeanMCP, query: str, top_k: int = 5) -> str:
    """Search for relevant lemmas using lean_local_search."""
    result = lsp.call("lean_local_search", query=query, max_results=top_k)
    return result.get("text", "")


def get_goal(lsp: LeanMCP, file_path: str, line: int, column: int = 0) -> str:
    """Get the proof goal at a specific location."""
    result = lsp.call("lean_goal", file_path=file_path, line=line, column=column)
    return result.get("text", "")


def multi_attempt(lsp: LeanMCP, file_path: str, line: int, snippets: list[str]) -> str:
    """Try multiple proof snippets and return results."""
    result = lsp.call("lean_multi_attempt",
                      file_path=file_path, line=line, snippets=snippets)
    return result.get("text", "")


def verify_code(lsp: LeanMCP, code: str, file_path: str | None = None) -> tuple[bool, str]:
    """Verify a code snippet using lean_run_code or lean_verify."""
    kwargs = {"code": code}
    if file_path:
        kwargs["file_path"] = file_path
    result = lsp.call("lean_run_code", **kwargs)
    text = result.get("text", "")
    ok = not result.get("isError", False) and "error" not in text.lower()
    return (ok, text)
