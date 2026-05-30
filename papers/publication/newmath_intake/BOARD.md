# Newmath Intake Board

This board is the human-facing index for newmath-derived publication seeds.
Machine-facing scheduling remains in `../PROGRAM_BOARD_MACHINE.md`; these
seeds are marked `INTAKE-NOT-ACTIVE` there and must not be picked up by
paper-stage automation until promoted.

| Seed | Priority | Target shape | Current status | Next action |
|---|---:|---|---|---|
| `bedc_automation_pipeline` | P0 | systems / automation paper | ready for human promotion decision; not promoted; CICM two-page packet prepared | Ask human whether to promote for CICM presentation-only as `2026_auditable_theory_to_paper_pipeline`; use `cicm_two_page_packet.md` after approval |
| `bedc_finite_kernel_calculus` | P0 | finite-kernel logic paper | exact statements read; not promoted | Use `packaging_theorem_proposal.md` to add/identify one upstream packaging theorem before journal-style promotion |
| `bedc_rule110_finite_witness` | P0 | artifact / minimal-trust witness paper | static recheck found count drift; no local build toolchain; not promoted | Use `build_environment_plan.md` to install/use `make` plus C compiler, run full suite, and resolve collision-audit contradiction |
| `metacic_closed_normal_consistency` | P1 | mechanized type-theory note | intake-ready | Audit related work and isolate the closed-normal consistency theorem boundary |
| `observer_state_semantics` | P1 | observer-state semantics / position paper | intake-ready | Reframe away from AI-consciousness claims and toward ledger-bounded semantics |

## Promotion Checklist

A seed may be promoted into a `2026_*` active paper track only when all entries
below are true.

- `seed_packet.md` states the proposed paper claim in one paragraph.
- `seed_packet.md` states non-claims explicitly.
- `source_map.md` pins `D:/omega/newmath` to a commit.
- `theorem_inventory.md` or `artifact_inventory.md` is specific enough for an
  agent to cite source paths and verification commands.
- `venue_ladder.md` has a primary venue and at least two fallback venues.
- `risk_register.md` includes kill criteria that prevent overclaiming.
- A human approves promotion and creates a `2026_*` paper directory.
