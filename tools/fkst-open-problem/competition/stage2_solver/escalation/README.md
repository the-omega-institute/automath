# SAIR-EQT2 codex escalation layer

The deterministic `../submission/solver.py` is a zero-LLM floor (sample_200 160/200, hard2 65/200).
This directory adds an **LLM escalation layer**: for each problem the solver leaves unsolved, run
`codex` in a **judge-in-the-loop** cycle (propose a Lean certificate → run the official Lean judge →
read the goal-state error → fix → repeat) until the judge accepts, or abstain. Nothing is trusted
without the judge; the output is either a machine-checked certificate or none.

## Results (independently re-verified under the official `DEFAULT_PROOF_POLICY`)

### Guided (codex is told the verdict) — an UPPER BOUND
| set | solo floor | + codex | total | still unsolved |
|---|---|---|---|---|
| sample_200 | 160/200 | +40 | **200/200** | — |
| hard2 | 65/200 | +133 | **198/200** | `hard2_0027`, `hard2_0051` |

173 / 175 previously-unsolved problems given a machine-checked Lean certificate.

### Blind (codex is NOT told the verdict; it self-decides) — the competition-relevant measure
- **18 / 19** on a spike of previously-unsolved problems, **0 wrong verdicts** (the one miss,
  `hard2_0009` a false case, *abstained* — left no certificate rather than answering wrong).
- For comparison, the published pure single-prompt LLM ceiling on the verdict-only task is
  ~**79% local / 55% official** balanced accuracy (see arXiv 2604.18897). This layer clears it on a
  strictly harder, proof-carrying task.

## Honest boundary (do NOT overstate)
- **Guided 200/198 is an upper bound** (the verdict was provided). The blind number is lower and is
  the honest, competition-relevant figure; the blind run here is a 19-problem spike, not the full set.
- This is the **LLM track**, distinct from the deterministic Solo floor (160/65).
- Scores are from a **local clone of the official runner**, not the hosted leaderboard.
  **Nothing has been submitted or registered.**
- **No new mathematics**: every problem has a known answer (the ETP resolved all of these); these
  certificates re-prove known facts. The contribution is a system/method, not a theorem.

## Files
- `run_escalation.py` — guided full-run orchestrator (resumable, cache-backed, daemonizable).
- `run_blind_spike.py` — blind spike orchestrator (codex self-decides the verdict).
- `verify_one.py` — single (problem, answer) check against `judge.verify.verify_answer`, injecting
  the official `DEFAULT_PROOF_POLICY` (mirrors `pipeline/proxy.py`).
- `SPIKE_INSTRUCTIONS.md` / `SPIKE_INSTRUCTIONS_BLIND.md` — the per-problem codex directives.
- `certs/guided_certs.jsonl` — 173 accepted guided certificates (`{id, set, eq*, equation*, truth,
  verdict, code}` per line).
- `certs/blind_certs.jsonl` — 18 accepted blind certificates.
- `results/guided_final.json`, `results/blind_spike.json`, `results/guided_final_sweep.json` — tallies.

## Reproduce
Requires an external checkout of the judge (not vendored, per FKST discipline):
```sh
git clone https://github.com/SAIRcompetition/equational-theories-lean-stage2 /path/eqt2-stage2
cd /path/eqt2-stage2 && SKIP_DOCKER=1 bash scripts/setup.sh   # builds local Lean judge
python3 -m venv .venv && .venv/bin/pip install openai         # runner imports openai
# place run_escalation.py / verify_one.py / run_blind_spike.py at the judge repo root, then:
source .env.judge && PYTHONDONTWRITEBYTECODE=1 .venv/bin/python run_escalation.py --daemon
```
Note: the harness scripts contain absolute paths from the run environment (judge root, a scratch work
dir); adjust the constants at the top of each before re-running elsewhere. macOS `/tmp` is purged on a
3-day cycle — keep the judge clone at a durable (non-`/tmp`) path.
