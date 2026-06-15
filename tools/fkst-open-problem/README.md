# FKST Open-Problem Automation Pilot

This directory records the first-pass integration plan for using ChronoAI's
`fkst` pipeline as an automation layer for Omega open-problem work.

The integration is intentionally narrow:

- `fkst` is used as an event supervisor, consensus router, and GitHub issue/PR
  state machine.
- Omega/Automath remains the source of mathematical truth. Durable claims must
  be committed as repository files, Lean certificates, JSON ledgers, or PRs.
- Runtime queues, logs, cache, and agent memory are scratch state only.
- The first pilot runs in dry-run mode. Real GitHub writes require explicit
  operator opt-in through `FKST_GITHUB_WRITE=1`.

## Upstream FKST Repositories

The relevant ChronoAI repositories as of 2026-06-15 are:

| Repository | Role | Notes |
| --- | --- | --- |
| `ChronoAIProject/fkst-substrate` | Rust runtime and fixed SDK surface | `SPEC.md` defines the Tier I/II/III boundary, reliable delivery, `spawn_codex`, `exec_sync`, and conformance. |
| `ChronoAIProject/fkst-packages` | Lua behavior packages | Provides `consensus`, `github-proxy`, `autochrono`, and `github-devloop`. |
| `ChronoAIProject/fkst-hosted` | Hosted package/session/goal API | Useful later if we want managed sessions instead of local substrate. |
| `ChronoAIProject/fkst-website` | Domain package example | Useful as a composed-package reference, not needed for the first pilot. |

## Fit Assessment

`fkst` is a good fit for orchestration, not for proof search itself.

Good matches:

- turning open-problem work units into durable GitHub issues;
- running bounded independent Codex attempts with `minimal`, `structural`, and
  `delete` style consensus;
- routing candidate progress through review/fix loops;
- requiring git/PR/Lean artifacts as the only accepted durable facts;
- recovering after process crashes by replaying GitHub/git state.

Bad matches:

- storing mathematical state inside the runtime queue or cache;
- treating consensus as a proof;
- letting a generic software-dev PR loop merge mathematical claims without Lean
  or source-replay evidence;
- directly supervising long-running exploratory search without a small,
  inspectable proposal boundary.

## Pilot Scope

The first pilot should target one narrow frontier where we already have a stable
artifact surface:

1. `T-43 / Problems I Like #2`
   - goal: source-replay the A5 Godeaux-Serre same-W rank-4 certificate
     candidate;
   - expected outputs: source ledger, Lean/source anchors, obstruction log, and
     a claim-state JSON record.
2. `T-44 / Problems I Like #4`
   - goal: preserve the KP2 stabilizer-fiber bridge refutation and avoid
     re-entering the dead route;
   - expected outputs: route-refutation record and replay checker.
3. `T-32 / Litt common finite etale cover`
   - goal: isolate the primitive C4 blocker into an auditable computation plan;
   - expected outputs: C4 representative audit manifest and missing-certificate
     gate.

The pilot should not attempt to solve all three at once. Use one issue per
proposal and one proposal per small certificate objective.

## Branch Policy

This branch is for FKST integration assets only:

- package skeletons;
- issue templates / seed proposals;
- runbook and risk notes;
- dry-run harnesses.

Do not vendor `fkst-substrate` or `fkst-packages` into this repository. Use
external checkouts or hosted sessions when running the engine.

## Dry-Run Environment

Recommended local dry-run variables:

```sh
export FKST_GITHUB_REPO=the-omega-institute/automath
export FKST_GITHUB_WRITE=0
export FKST_DEVLOOP_UPSTREAM_BRANCH=dev-automation-integration
export FKST_DEVLOOP_INTEGRATION_BRANCH=codex/fkst-open-problem-automation
export FKST_DEVLOOP_TEST_COMMAND='python3 tools/fkst-open-problem/scripts/check_seed.py'
```

For a real supervisor, also provide host-local runtime roots:

```sh
export FKST_RUNTIME_ROOT=/tmp/fkst-omega-runtime
export FKST_DURABLE_ROOT=/tmp/fkst-omega-durable
export FKST_RATE_POOL_ROOT=/tmp/fkst-omega-rate-pools
```

These roots must remain untracked.

## Acceptance Bar

An FKST-generated mathematical contribution is acceptable only when it leaves
one of the following durable artifacts:

- a Lean file or Lean anchor that builds;
- a replayable Python/Sage/checker script with a JSON output ledger;
- a route-refutation record with explicit assumptions and reproduction steps;
- a claim-state metadata update that says exactly what is proved, blocked, or
  only conjectural;
- a PR containing one of the above plus a reviewable summary.

Agent consensus alone is never an accepted mathematical fact.
