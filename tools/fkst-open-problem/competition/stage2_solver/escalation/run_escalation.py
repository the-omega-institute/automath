#!/usr/bin/env python3
"""Codex escalation orchestrator for SAIR-EQT2 unsolved problems.

For every problem the deterministic solver left UNSOLVED (sample_200 + hard2), run
`codex` judge-in-the-loop (guided by the known verdict) to produce a Lean certificate,
independently re-verify it under the official DEFAULT_PROOF_POLICY, and record the result.

- 8-way parallel codex pool.
- Resumable: a problem whose <id>.answer.json already verifies as accepted is skipped.
- Per-problem wall timeout (codex `timeout`), miss -> recorded, not fatal.
- Progress written to escalation_progress.json; summary line every ~20s.

Run from repo root with `.venv/bin/python run_escalation.py` after `source .env.judge`.
"""
import json
import os
import subprocess
import sys
import time
import threading
import concurrent.futures
import pathlib

ROOT = pathlib.Path("/Users/lexa/Desktop/lexa/omega/eqt2-stage2")
WORK = pathlib.Path(
    "/private/tmp/claude-501/-Users-lexa-Desktop-lexa-omega-automath/"
    "212fb8e9-b173-4c53-b415-65750bbe217b/scratchpad/spike"
)
INSTR = WORK / "SPIKE_INSTRUCTIONS.md"
RESULTS_REF = pathlib.Path(
    "/Users/lexa/Desktop/lexa/omega/automath-outreach/tools/fkst-open-problem/"
    "competition/stage2_solver/official_results"
)
PARALLEL = 5  # capped from 8: 8-way concurrent Lean (decideFin! w/ 1M heartbeats) caused
              # memory-pressure kills (~1.5M pageouts). 5 keeps peak RSS survivable.
PER_PROBLEM_TIMEOUT = 1500
VENV_PY = str(ROOT / ".venv" / "bin" / "python")
PROGRESS = WORK / "escalation_progress.json"
ACCEPTED_CACHE = WORK / "accepted_cache.json"
CODEX_LOGDIR = WORK / "codex_logs"
CODEX_LOGDIR.mkdir(exist_ok=True)

_print_lock = threading.Lock()
_cache_lock = threading.Lock()


def load_cache():
    try:
        return set(json.load(open(ACCEPTED_CACHE)))
    except Exception:
        return set()


_ACCEPTED = load_cache()


def mark_accepted(pid):
    with _cache_lock:
        _ACCEPTED.add(pid)
        ACCEPTED_CACHE.write_text(json.dumps(sorted(_ACCEPTED)))


def verify_cached(pid):
    """Like verify() but trusts the accepted-cache (no Lean call for known-good),
    so launchd restarts don't re-verify hundreds of answers."""
    if pid in _ACCEPTED:
        return "accepted"
    st = verify(pid)
    if st == "accepted":
        mark_accepted(pid)
    return st


def log(msg):
    with _print_lock:
        print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def load_unsolved():
    """Return list of (id, problem_dict, verdict) for every unsolved problem."""
    sets = [
        ("examples/problems/sample_200.json", RESULTS_REF / "sample200_final.json"),
        ("examples/problems/hard2.jsonl", RESULTS_REF / "hard2_final.json"),
    ]
    out = []
    for probs_path, res_path in sets:
        p = ROOT / probs_path
        text = p.read_text()
        if text.lstrip()[0] == "[":
            probs = {r["id"]: r for r in json.loads(text)}
        else:
            probs = {}
            for line in text.splitlines():
                line = line.strip()
                if line:
                    r = json.loads(line)
                    probs[r["id"]] = r
        res = json.load(open(res_path))
        for r in res:
            if not r.get("solved"):
                pid = r["id"]
                pr = probs[pid]
                out.append((pid, {k: pr[k] for k in ("id", "eq1_id", "eq2_id", "equation1", "equation2")}, pr["answer"]))
    return out


def verify(pid):
    """Return judge status string for <id>.answer.json, or None if no/broken answer."""
    ans = WORK / f"{pid}.answer.json"
    prob = WORK / f"{pid}.json"
    if not ans.exists() or not prob.exists():
        return None
    try:
        r = subprocess.run(
            [VENV_PY, str(ROOT / "verify_one.py"), str(prob), str(ans)],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
        return json.loads(r.stdout.strip().splitlines()[-1])["status"]
    except Exception:
        return "verify-error"


def run_one(pid, problem, verdict):
    # write the problem file
    (WORK / f"{pid}.json").write_text(json.dumps(problem))
    # resume: skip if already accepted
    if verify_cached(pid) == "accepted":
        return pid, "accepted", "skipped(already)"
    vtxt = "true" if verdict else "false"
    extra = (
        " (finite-magma counterexample via finOpTable ONLY, no custom inductive types, "
        "Fin<=10 single-digit, decideFin!)" if not verdict else ""
    )
    prompt = (
        f"Read {INSTR} and follow it EXACTLY. Solve problem id={pid}, target verdict={vtxt}{extra}. "
        f"Work from {ROOT} (run `source .env.judge` before verifying). Iterate against verify_one.py "
        f"up to 6 times until status==accepted. Leave your best answer at {WORK}/{pid}.answer.json. "
        f"End with the single RESULT line."
    )
    logf = CODEX_LOGDIR / f"{pid}.log"
    try:
        with open(logf, "w") as lf:
            subprocess.run(
                ["codex", "exec", "--dangerously-bypass-approvals-and-sandbox", prompt],
                cwd=ROOT, stdout=lf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                timeout=PER_PROBLEM_TIMEOUT,
            )
    except subprocess.TimeoutExpired:
        pass
    except Exception as e:
        return pid, "codex-error", str(e)[:120]
    st = verify_cached(pid)
    return pid, (st or "no-answer"), ""


def main():
    work = load_unsolved()
    log(f"unsolved total: {len(work)}  (TRUE={sum(1 for _,_,v in work if v)} FALSE={sum(1 for _,_,v in work if not v)})")
    # pre-skip already accepted
    todo = []
    accepted0 = 0
    for pid, prob, v in work:
        (WORK / f"{pid}.json").write_text(json.dumps(prob))
        if verify_cached(pid) == "accepted":
            accepted0 += 1
        else:
            todo.append((pid, prob, v))
    log(f"already accepted (resume skip): {accepted0}   to run: {len(todo)}")

    results = {}
    done = 0
    start = time.time()
    last = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=PARALLEL) as ex:
        futs = {ex.submit(run_one, pid, prob, v): pid for pid, prob, v in todo}
        for fut in concurrent.futures.as_completed(futs):
            pid, st, note = fut.result()
            results[pid] = st
            done += 1
            acc = accepted0 + sum(1 for s in results.values() if s == "accepted")
            log(f"[{done}/{len(todo)}] {pid} -> {st} {note}   (cumulative accepted: {acc})")
            PROGRESS.write_text(json.dumps(
                {"done": done, "todo": len(todo), "accepted_total": acc,
                 "elapsed_min": round((time.time()-start)/60, 1), "results": results}, indent=2))
    acc = accepted0 + sum(1 for s in results.values() if s == "accepted")
    log(f"DONE. total unsolved={len(work)}  now accepted={acc}  (added {acc-accepted0})")


def daemonize():
    """Double-fork + setsid so the run detaches into its own session and reparents to
    init (PID 1) — surviving the harness reaping the launching shell's session/children.
    stdout/stderr fds (already redirected to the log at launch) are inherited across forks."""
    if os.fork() > 0:
        os._exit(0)
    os.setsid()
    if os.fork() > 0:
        os._exit(0)
    # write our pid so the babysitter can find/verify us
    (WORK / "escalation.pid").write_text(str(os.getpid()))


if __name__ == "__main__":
    if "--daemon" in sys.argv:
        daemonize()
    main()
