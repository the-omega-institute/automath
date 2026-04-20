#!/usr/bin/env python3
"""Concurrency-limited wrapper around `lake`.

All worktrees opened by `codex_formalize.py` share a single host (16 GB M3
unified memory in our case). Letting N parallel rounds each invoke
`lake build` simultaneously starves the kernel watchdog and panics the box
(the 2026-04-18 AppleARMWatchdogTimer incident).

This wrapper enforces a hard upper bound on concurrent `lake` invocations
across ALL worktrees by acquiring one of `LAKE_GATE_MAX_PARALLEL` advisory
locks. Pure flock-based, no extra dependencies, works between unrelated
processes (codex CLI invocations from separate worker threads, manual
`python3 lake_gate.py build …` from a shell, etc.).

Usage from the shell:
    python3 lean4/scripts/lake_gate.py build
    python3 lean4/scripts/lake_gate.py build Omega.X.Y
    python3 lean4/scripts/lake_gate.py env -- lean --version

Config (env vars, all optional):
    LAKE_GATE_MAX_PARALLEL    int, default 1 — concurrent `lake` ceiling
    LAKE_GATE_LOCK_DIR        path, default $TMPDIR/automath-lake-gate
    LAKE_GATE_POLL_SECONDS    float, default 5.0 — slot retry interval
    LAKE_GATE_WAIT_TIMEOUT    float, default 14400 — give up after this many
                              seconds of waiting for a slot
    LAKE_GATE_MEM_GUARD       0/1, default 1 on darwin — pause when macOS
                              memory pressure is elevated
    LAKE_GATE_MEM_THRESHOLD   int, default 2 — pressure level (1=NORMAL,
                              2=WARN, 4=URGENT, 8=CRITICAL) at or above
                              which we wait
    LAKE_GATE_VERBOSE         0/1, default 1 — log slot acquire/release
"""

from __future__ import annotations

import argparse
import errno
import fcntl
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def _env_int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, str(default)))
    except ValueError:
        return default


def _env_float(name: str, default: float) -> float:
    try:
        return float(os.environ.get(name, str(default)))
    except ValueError:
        return default


def _env_bool(name: str, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return default
    return raw.strip() not in ("", "0", "false", "False", "no", "off")


MAX_PARALLEL = max(1, _env_int("LAKE_GATE_MAX_PARALLEL", 1))
LOCK_DIR = Path(
    os.environ.get(
        "LAKE_GATE_LOCK_DIR",
        str(Path(tempfile.gettempdir()) / "automath-lake-gate"),
    )
)
POLL_SECONDS = max(0.5, _env_float("LAKE_GATE_POLL_SECONDS", 5.0))
WAIT_TIMEOUT = max(60.0, _env_float("LAKE_GATE_WAIT_TIMEOUT", 14400.0))
MEM_GUARD = _env_bool("LAKE_GATE_MEM_GUARD", sys.platform == "darwin")
MEM_THRESHOLD = max(2, _env_int("LAKE_GATE_MEM_THRESHOLD", 2))
VERBOSE = _env_bool("LAKE_GATE_VERBOSE", True)


def _log(msg: str) -> None:
    if VERBOSE:
        print(f"[lake_gate pid={os.getpid()}] {msg}", file=sys.stderr, flush=True)


def _macos_pressure_level() -> int:
    if sys.platform != "darwin":
        return 0
    try:
        r = subprocess.run(
            ["sysctl", "-n", "kern.memorystatus_vm_pressure_level"],
            capture_output=True, text=True, timeout=5,
            stdin=subprocess.DEVNULL,
        )
        return int((r.stdout or "0").strip() or "0")
    except Exception:
        return 0


def _wait_for_memory() -> None:
    if not MEM_GUARD:
        return
    deadline = time.time() + WAIT_TIMEOUT
    warned = False
    while True:
        level = _macos_pressure_level()
        if level == 0 or level < MEM_THRESHOLD:
            if warned:
                _log(f"memory pressure cleared (level={level}); proceeding")
            return
        if time.time() > deadline:
            _log(f"memory pressure {level} but timeout; proceeding anyway")
            return
        if not warned:
            _log(f"memory pressure {level} >= {MEM_THRESHOLD}; pausing lake")
            warned = True
        time.sleep(POLL_SECONDS)


def _try_acquire(slot_path: Path):
    """Try to acquire one slot. Returns the open fd on success, None on failure."""
    fd = os.open(str(slot_path), os.O_CREAT | os.O_RDWR, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError as exc:
        os.close(fd)
        if exc.errno in (errno.EWOULDBLOCK, errno.EAGAIN, errno.EACCES):
            return None
        raise
    # Stamp the slot for forensics.
    try:
        os.ftruncate(fd, 0)
        os.write(fd, f"{os.getpid()} {time.time():.1f}\n".encode())
        os.fsync(fd)
    except OSError:
        pass
    return fd


def _acquire_any_slot() -> tuple[int, Path]:
    LOCK_DIR.mkdir(parents=True, exist_ok=True)
    deadline = time.time() + WAIT_TIMEOUT
    announced_wait = False
    while True:
        # Try every slot in random order so contending callers don't pile up
        # on the same one.
        slot_indices = list(range(1, MAX_PARALLEL + 1))
        # Mild randomization without importing random: shift by pid mod N.
        offset = os.getpid() % MAX_PARALLEL
        slot_indices = slot_indices[offset:] + slot_indices[:offset]
        for i in slot_indices:
            slot = LOCK_DIR / f"slot-{i}"
            fd = _try_acquire(slot)
            if fd is not None:
                _log(f"acquired {slot.name} (max_parallel={MAX_PARALLEL})")
                return fd, slot
        if time.time() > deadline:
            raise SystemExit(
                f"lake_gate: timed out after {WAIT_TIMEOUT:.0f}s waiting for one of "
                f"{MAX_PARALLEL} slot(s) under {LOCK_DIR}"
            )
        if not announced_wait:
            _log(
                f"all {MAX_PARALLEL} slot(s) busy under {LOCK_DIR}; "
                f"polling every {POLL_SECONDS:.1f}s"
            )
            announced_wait = True
        time.sleep(POLL_SECONDS)


def _release_slot(fd: int, slot: Path) -> None:
    try:
        fcntl.flock(fd, fcntl.LOCK_UN)
    except OSError:
        pass
    try:
        os.close(fd)
    except OSError:
        pass
    _log(f"released {slot.name}")


def _exec_lake(forwarded: list[str]) -> int:
    lake = shutil.which("lake")
    if not lake:
        print("lake_gate: `lake` not found in PATH", file=sys.stderr)
        return 127
    cmd = [lake, *forwarded]
    _log(f"running: {' '.join(cmd)} (cwd={os.getcwd()})")
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, stdin=subprocess.DEVNULL)
    except KeyboardInterrupt:
        return 130
    elapsed = time.monotonic() - start
    _log(f"lake exited rc={proc.returncode} in {elapsed:.1f}s")
    return proc.returncode


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Concurrency-limited lake wrapper",
        usage="%(prog)s [lake-args...]",
        add_help=False,  # forward --help to lake when explicit
    )
    parser.add_argument("--gate-help", action="store_true",
                        help="Show lake_gate's own help and exit")
    parser.add_argument("--gate-status", action="store_true",
                        help="Print current slot occupancy and exit (no lake call)")
    args, forwarded = parser.parse_known_args()

    if args.gate_help:
        print(__doc__)
        return 0

    if args.gate_status:
        if not LOCK_DIR.exists():
            print(f"lock dir {LOCK_DIR} does not exist (no slots held)")
            return 0
        for slot in sorted(LOCK_DIR.glob("slot-*")):
            try:
                fd = os.open(str(slot), os.O_RDWR)
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    fcntl.flock(fd, fcntl.LOCK_UN)
                    state = "free"
                except OSError:
                    state = "HELD"
                os.close(fd)
            except OSError as exc:
                state = f"err({exc})"
            content = ""
            try:
                content = slot.read_text(errors="replace").strip()
            except OSError:
                pass
            print(f"  {slot.name}: {state}  {content}")
        return 0

    if not forwarded:
        print("lake_gate: nothing to run (forward args to lake, e.g. `build`)",
              file=sys.stderr)
        return 64

    # Forward SIGTERM/SIGINT so cancellation propagates to lake itself.
    def _passthrough(signum, _frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, _passthrough)

    fd, slot = _acquire_any_slot()
    try:
        _wait_for_memory()
        return _exec_lake(forwarded)
    finally:
        _release_slot(fd, slot)


if __name__ == "__main__":
    sys.exit(main())
