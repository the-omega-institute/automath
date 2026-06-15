# FKST Pilot: Omega Open Problems

## Decision

Use FKST as an automation substrate for open-problem advancement, with a
dry-run first stage. The most valuable FKST capability is not proof generation;
it is reliable proposal routing, consensus, implementation attempts, PR review
loops, and crash recovery from GitHub/git facts.

## Why It Fits

Omega open-problem work has the shape FKST expects:

- small proposals can be represented as GitHub issues or queue events;
- progress should become git facts, not runtime facts;
- multiple agent angles are useful before committing to a route;
- bad routes should become durable refutation records;
- every positive claim needs a replay artifact.

This is especially useful for frontier tasks where the main risk is route
selection and stale state, not raw compute.

## Why It Needs Constraints

FKST's `github-devloop` was designed for software implementation loops. For
mathematics, the merge gate must be stricter:

- a PR with prose alone is not enough;
- a consensus `approve` is not enough;
- a Codex-generated proof sketch is not enough;
- accepted output must be a Lean/checker/source-replay artifact, or a clearly
  scoped obstruction/refutation record.

## First Pilot

Start with T-43 rather than T-32 or T-44.

T-43 has a concrete candidate artifact: the A5 Godeaux-Serre rank-4 standard
same-W certificate candidate. The FKST task can be narrow:

1. decompose the candidate into source obligations;
2. classify each obligation as confirmed, missing, false, or external;
3. write a claim-state record;
4. produce no theorem claim unless source replay closes.

T-44 is a good second task because FKST can preserve a route refutation. T-32 is
third because it has heavier computation prerequisites.

## Proposed Runtime Shape

Use external checkouts:

```text
../fkst-substrate
../fkst-packages
this repo: tools/fkst-open-problem/packages/omega-open-problem
```

Run composed with package roots:

```text
--package-root ../fkst-packages/packages/consensus
--package-root tools/fkst-open-problem/packages/omega-open-problem
```

For GitHub-driven work later, compose with `github-proxy` and `github-devloop`
instead of the simple seed raiser.

## First Dry-Run Test

The first dry-run should only validate event shape:

1. raiser `seed` emits `omega_proposal`;
2. department `proposal_intake` validates it;
3. department raises `consensus.proposal`;
4. no GitHub writes occur.

## Real-Write Gate

Do not set `FKST_GITHUB_WRITE=1` until:

- package conformance passes;
- dry-run events show the expected consensus proposal;
- a test command verifies the produced artifact type;
- branch protection and PR review policy are understood for the target repo.
