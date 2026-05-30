# Newmath Intake Board

This board is the human-facing index for newmath-derived publication seeds.
Machine-facing scheduling remains in `../PROGRAM_BOARD_MACHINE.md`; these
seeds are marked `INTAKE-NOT-ACTIVE` there and must not be picked up by
paper-stage automation until promoted.

| Seed | Priority | Target shape | Current status | Next action |
|---|---:|---|---|---|
| `bedc_automation_pipeline` | P0 | systems / automation paper | intake-ready | Write a scope contract around audit-driven AI formalization and theory-to-paper automation |
| `bedc_finite_kernel_calculus` | P0 | finite-kernel logic paper | intake-ready | Extract a theorem inventory for marks, histories, continuations, packages, gaps, and NameCert |
| `bedc_rule110_finite_witness` | P0 | artifact / minimal-trust witness paper | intake-ready | Convert Rule 110 status data into an artifact inventory and limitation ledger |
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

