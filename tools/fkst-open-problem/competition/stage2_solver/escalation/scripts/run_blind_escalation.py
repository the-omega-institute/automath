#!/usr/bin/env python3
"""BLIND spike: codex is NOT told the verdict; it must decide true/false itself, produce a
judge-accepted certificate, and we score it. Measures the real (competition-relevant) blind
hit rate of the hybrid on a sample of the previously-unsolved problems.

Sample: 7T+3F from sample_200-unsolved and 7T+3F from hard2-unsolved = 20 problems.
Daemonized, PARALLEL=5, resumable via accepted-cache.
"""
import argparse
import concurrent.futures
import json
import os
import pathlib
import subprocess
import time
import threading

import run_guided_escalation as R  # reuse configure, load_unsolved

ARTIFACT_ROOT = pathlib.Path(__file__).resolve().parents[1]
VERIFY_ONE = pathlib.Path(__file__).resolve().with_name("verify_one.py")

ROOT = None
VENV_PY = None
BASE = None
INSTR = ARTIFACT_ROOT / "prompts" / "SPIKE_INSTRUCTIONS_BLIND.md"
CODEX_LOGDIR = None
PROGRESS = None
CACHE = None
PARALLEL = 5
PER_PROBLEM_TIMEOUT = 1500
_lock = threading.Lock()


def build_parser():
    parser = argparse.ArgumentParser(
        description="Run blind Codex escalation over a deterministic residual spike."
    )
    parser.add_argument("--judge-root", required=True, type=pathlib.Path,
                        help="Local checkout of equational-theories-lean-stage2.")
    parser.add_argument("--work-dir", required=True, type=pathlib.Path,
                        help="Scratch directory for per-problem files, answers, and logs.")
    parser.add_argument("--results-ref", required=True, type=pathlib.Path,
                        help="Directory containing deterministic residual id lists.")
    parser.add_argument("--parallel", type=int, default=5,
                        help="Concurrent Codex jobs. Default: 5.")
    parser.add_argument("--timeout", type=int, default=1500,
                        help="Per-problem Codex wall timeout in seconds. Default: 1500.")
    parser.add_argument("--venv-python", default=None,
                        help="Python interpreter for judge verification. Default: <judge-root>/.venv/bin/python.")
    parser.add_argument("--daemon", action="store_true",
                        help="Detach before running.")
    parser.add_argument("--full", action="store_true",
                        help="Run the FULL blind benchmark over all residuals (default: 19-problem spike).")
    return parser


def configure(args):
    global ROOT, VENV_PY, BASE, CODEX_LOGDIR, PROGRESS, CACHE
    global PARALLEL, PER_PROBLEM_TIMEOUT

    R.configure(args)
    ROOT = R.ROOT
    VENV_PY = R.VENV_PY
    BASE = args.work_dir.resolve()
    PARALLEL = args.parallel
    PER_PROBLEM_TIMEOUT = args.timeout
    CODEX_LOGDIR = BASE / "codex_logs"
    PROGRESS = BASE / "blind_progress.json"
    CACHE = BASE / "accepted_cache.json"
    BASE.mkdir(parents=True, exist_ok=True)
    CODEX_LOGDIR.mkdir(parents=True, exist_ok=True)


def log(m):
    with _lock:
        print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)


def pick_sample():
    work = {i: (prob, v) for i, prob, v in R.load_unsolved()}
    s_t = [i for i in work if not i.startswith("hard2") and work[i][1]][:7]
    s_f = [i for i in work if not i.startswith("hard2") and not work[i][1]][:3]
    h_t = [i for i in work if i.startswith("hard2") and work[i][1]][:7]
    h_f = [i for i in work if i.startswith("hard2") and not work[i][1]][:3]
    ids = s_t + s_f + h_t + h_f
    return [(i, work[i][0], work[i][1]) for i in ids]


def verify(pid):
    ans = BASE / f"{pid}.answer.json"; prob = BASE / f"{pid}.json"
    if not ans.exists():
        return None, None
    try:
        r = subprocess.run([VENV_PY, str(VERIFY_ONE), "--judge-root", str(ROOT), str(prob), str(ans)],
                           cwd=ROOT, capture_output=True, text=True, timeout=120)
        st = json.loads(r.stdout.strip().splitlines()[-1])["status"]
        chosen = json.load(open(ans)).get("verdict")
        return st, chosen
    except Exception:
        return "verify-error", None


def run_one(pid, problem, truth):
    (BASE / f"{pid}.json").write_text(json.dumps(problem))
    st, chosen = verify(pid)
    if st != "accepted":
        prompt = (f"Read {INSTR} and follow it EXACTLY (BLIND — you are NOT told the answer). "
                  f"Solve problem id={pid}. Work from {ROOT} (run `source .env.judge` before verifying). "
                  f"Determine the verdict yourself, iterate against verify_one.py up to 8 times until "
                  f"status==accepted. Leave your best answer at {BASE}/{pid}.answer.json. End with the RESULT line.")
        try:
            with open(CODEX_LOGDIR / f"{pid}.log", "w") as lf:
                subprocess.run(["codex", "exec", "--dangerously-bypass-approvals-and-sandbox", prompt],
                               cwd=ROOT, stdout=lf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                               timeout=PER_PROBLEM_TIMEOUT)
        except subprocess.TimeoutExpired:
            pass
        except Exception as e:
            return pid, "codex-error", None, truth
        st, chosen = verify(pid)
    correct_verdict = (chosen == ("true" if truth else "false")) if chosen else None
    return pid, (st or "no-answer"), correct_verdict, truth


def daemonize():
    if os.fork() > 0: os._exit(0)
    os.setsid()
    if os.fork() > 0: os._exit(0)
    (BASE / "blind.pid").write_text(str(os.getpid()))


def main():
    parser = build_parser()
    args = parser.parse_args()
    configure(args)
    if args.daemon:
        daemonize()

    sample = R.load_unsolved() if args.full else pick_sample()
    mode = "full" if args.full else "spike"
    log(f"BLIND {mode}: {len(sample)} problems ({sum(1 for _,_,v in sample if v)} true / {sum(1 for _,_,v in sample if not v)} false)")
    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=PARALLEL) as ex:
        futs = {ex.submit(run_one, i, p, v): i for i, p, v in sample}
        done = 0
        for fut in concurrent.futures.as_completed(futs):
            pid, st, correct, truth = fut.result()
            results[pid] = {"status": st, "correct_verdict": correct, "truth": truth}
            done += 1
            acc = sum(1 for r in results.values() if r["status"] == "accepted")
            log(f"[{done}/{len(sample)}] {pid} -> {st} (verdict_correct={correct}) | accepted={acc}")
            PROGRESS.write_text(json.dumps({"done": done, "total": len(sample),
                                            "accepted": acc, "results": results}, indent=2))
    acc = sum(1 for r in results.values() if r["status"] == "accepted")
    log(f"BLIND DONE. accepted={acc}/{len(sample)}")


if __name__ == "__main__":
    main()
