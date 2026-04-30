# Automath Outreach Log

## Active Targets

| Target | Channel | Status | Backflow | Best Score | Last Update |
|---|---|---|---|---|---|
| google-deepmind/formal-conjectures | GitHub PR | Stage B hold — source/publication gate | — | 3/10 | 2026-04-29 |
| Erdős #475 / Graham valid orderings | erdosproblems forum/PR (gated) | draft ready, Claude-reviewed — p≤23 certificates verified, p=29 samples 500/500 | — | 8/10 | 2026-04-30 |
| Erdős #199 / Minimum Overlap | erdosproblems forum/arXiv (gated) | supervised — White-style certificate engine needed | — | 7/10 | 2026-04-30 |
| OPG Lucas mod m complete residues | OPG/email (gated) | Stage C ready — local verifier m≤100000, 0 mismatches | — | 8/10 | 2026-04-30 |
| Heath Sanchez | SAIR Zulip | draft ready | — | — | 2026-04-18 |
| Israel Cazares | SAIR Zulip | draft ready | — | — | 2026-04-19 |
| Israel (bytepro.ai) — single-prompt ceiling × structural invariants | Email (hello@bytepro.ai) | sent 2026-04-30 — collab proposal + arXiv endorsement ask (math.DS / math.CO / math.LO / cs.AI), reply pending | — | — | 2026-04-30 |
| Terence Tao | Email | planned wk3-4 | — | — | — |

## Completed

| Target | Channel | Result | Date |
|---|---|---|---|
| teorth/analysis | GitHub issue | [#494](https://github.com/teorth/analysis/issues/494) | 2026-04-24 |
| teorth/equational_theories #364 — countermodel | GitHub issue comment | [comment](https://github.com/teorth/equational_theories/issues/364#issuecomment-4313955597) | 2026-04-24 |
| teorth/equational_theories #364 — affine closure + non-affine witness | GitHub issue comment | [comment](https://github.com/teorth/equational_theories/issues/364#issuecomment-4313957801) | 2026-04-24 |
| the-omega-institute/automath #38 — Tolmeton reply: BF citation diagram + co-author probe | GitHub issue comment | [comment](https://github.com/the-omega-institute/automath/issues/38#issuecomment-4353065430) | 2026-04-30 |
| the-omega-institute/automath #38 — nonneg lift follow-up | GitHub issue comment | [comment](https://github.com/the-omega-institute/automath/issues/38#issuecomment-4313959985) | 2026-04-24 |
| the-omega-institute/automath #38 — signed companion audit | GitHub issue comment | [comment](https://github.com/the-omega-institute/automath/issues/38#issuecomment-4298430964) | 2026-04-23 |
| teorth/equational_theories #418 | GitHub issue reply | [comment](https://github.com/teorth/equational_theories/issues/418#issuecomment-4289701235) | 2026-04-21 |
| teorth/equational_theories #364 | GitHub PR | [PR #1435](https://github.com/teorth/equational_theories/pull/1435) | 2026-04-22 |
| mysticflounder/equational-magma-theorems | GitHub issue #1 | [submitted](https://github.com/mysticflounder/equational-magma-theorems/issues/1) | 2026-04-15 |

## Pending Claude Review

| ID | Source | Content | Score | Verdict |
|---|---|---|---|---|
| c62ec | #38 future | all-q exterior-Lucas obstruction (partial) | 7/10 | hold — structural bound unproved |

## Backflow Tracking

| Target | Paper Section | Scripts | Date |
|---|---|---|---|
| #364 countermodel | appendix/window6_countermodel_certificate | scripts/equational_theory/audit_window6_current.py | 2026-04-22 |
| #38 signed companion | appendix/signed_companion_collision_audit | scripts/equational_theory/signed_companion_collision_audit.py | 2026-04-22 |
| #38 nonneg lift (797e) | appendix/signed_companion_collision_audit | scripts/equational_theory/nonnegative_lift_flow_certificate.py | 2026-04-24 |
| ETP stable arithmetic | appendix/stable_arithmetic_equational_audit | scripts/equational_theory/stable_arithmetic_facts.py | 2026-04-22 |
| ETP integral affine (57155) | appendix/stable_arithmetic_equational_audit | scripts/equational_theory/integral_affine_closure.py | 2026-04-24 |
| ETP non-affine witness (8eab) | appendix/stable_arithmetic_equational_audit | scripts/equational_theory/non_affine_finite_witness.py | 2026-04-24 |
| teorth/analysis | appendix/finite_conditional_expectation | — | 2026-04-22 |
| teorth #418 | body/finite_field_equational_saturation | scripts/equational_theory/*.py | 2026-04-21 |

## Pipeline Stats

| Metric | Value |
|---|---|
| Pipeline version | v23 (+ backflow language gate, Claude review integration, research-board supervisor) |
| Total submissions | 8 (4 ETP, 1 analysis, 1 automath, 1 mysticflounder, 1 PR) |
| Backflows to paper | 8 appendix sections |
| Pending | 1 (c62ec partial, holding) |
| Active targets | 7 (formal-conjectures, T-01, T-02, T-08, 2 Zulip, Tao email) |
