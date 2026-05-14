#!/usr/bin/env python3
"""Regression tests for prompt-echo Oracle extraction failures."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
GATE_PATH = REPO / "tools/community-outreach/outreach_oracle_response_gate.py"
CONSULTANT_PATH = REPO / "tools/community-outreach/oracle_consultant.py"
LOOP_PATH = REPO / "tools/community-outreach/outreach_research_loop.py"


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


PROMPT_ECHO = """You are the primary mathematical worker on this Omega Project outreach target.
This is not an outreach-copywriting task. The goal is a genuine mathematical contribution.

## Current Codex-selected task
Codex has already processed the local target directory.

## Codex local workup
# Codex Workup

## Compact science contract
Contribution type: research_note

## Target
- TODO id: T-43

## Math problem statement
Let f: X -> Y be smooth proper.

## Current deterministic science-gate blockers
- verification gate: verification_status=unverified

## Your first turn
Give the first contract-driven research step. Use this exact structure:
  1. CONTRACT TARGET: the precise theorem/counterexample/construction/certificate being attempted.
  2. CURRENT SCORE: the current value/state of the progress metric.
  3. MOVE: one concrete proof move.
  4. EVIDENCE: what artifact would verify this move.
  5. NEXT STOP TEST: whether the next turn should write back, continue, or close/re-scope.
Do not summarize the problem back to me. Start doing the mathematics.
"""


SHORT_PROMPT_ECHO = """You are the Oracle math worker for this Omega Project open-problem target.
Goal: make a genuine mathematical contribution, not outreach copy.

## Selected Task
Prove or obstruct the next local gap.

## Local Facts
Codex checked a local verifier and found a blocked formal reduction.

## Compact science contract
Verifier: proof, counterexample, computation, or valuable obstruction.

## Target
- ID: T-43
- Source: https://www.problemsilike.com/2

## Problem Statement
Let f: X -> Y be smooth proper.

## Deterministic Gate Blockers
- verification gate: verification_status=unverified

## Output
Use exactly:
1. CONTRACT TARGET:
2. CURRENT SCORE:
3. MOVE:
4. EVIDENCE:
5. NEXT STOP TEST:
Do not summarize or restart. Start with the next mathematical move.
"""


REAL_ANSWER = """1. CONTRACT TARGET: prove the rank-one geometric-summand reduction under finite determinant.
2. CURRENT SCORE: the summand-to-ambient Katz route is blocked by a direct-sum toy obstruction.
3. MOVE: use the Picard-Vessiot Galois group of the rank-one summand and Katz's theorem for algebraic solutions.
4. EVIDENCE: a lemma reducing the rank-one case to finite-order residues.
5. NEXT STOP TEST: continue unless Codex can replay the residue calculation.

Theorem. Let E be a rank-one logarithmic connection with rational residues. If its p-curvature vanishes for almost all primes, then each residue is rational with denominator supported only on excluded primes, hence the local monodromy is finite after a finite etale cover. Proof. This is substantive mathematical prose, not a prompt echo.
"""


def main() -> int:
    sys.path.insert(0, str(REPO / "tools/community-outreach"))
    gate = _load(GATE_PATH, "outreach_oracle_response_gate_under_test")
    consultant = _load(CONSULTANT_PATH, "oracle_consultant_under_test")
    loop = _load(LOOP_PATH, "outreach_research_loop_under_test")

    if not gate.is_prompt_echo_response(PROMPT_ECHO):
        raise AssertionError("prompt echo was not detected")
    if not gate.is_prompt_echo_response(SHORT_PROMPT_ECHO):
        raise AssertionError("short prompt echo was not detected")
    if not gate.is_non_substantive_oracle_response(PROMPT_ECHO):
        raise AssertionError("prompt echo should be non-substantive")
    if not consultant._is_transport_stub_response(PROMPT_ECHO):
        raise AssertionError("consultant should reject prompt echo as transport/extraction failure")
    if not loop._is_transport_stub_response(PROMPT_ECHO):
        raise AssertionError("research loop should reject prompt echo as transport/extraction failure")
    if consultant.is_outreach_response_valid(PROMPT_ECHO):
        raise AssertionError("prompt echo should not be a valid outreach response")
    if consultant.is_outreach_response_valid(SHORT_PROMPT_ECHO):
        raise AssertionError("short prompt echo should not be a valid outreach response")

    if gate.is_prompt_echo_response(REAL_ANSWER):
        raise AssertionError("real answer incorrectly classified as prompt echo")
    if gate.is_non_substantive_oracle_response(REAL_ANSWER):
        raise AssertionError("real answer incorrectly classified as non-substantive")
    if consultant._is_transport_stub_response(REAL_ANSWER):
        raise AssertionError("consultant incorrectly rejected real answer")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
