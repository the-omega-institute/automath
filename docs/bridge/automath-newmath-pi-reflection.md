# Automath-NewMath PI Reflection

This report is the deterministic PI layer for the NewMath-to-Automath bridge.
It turns global bridge and ACK signals into disciplined Killo/golden writeback control actions.
It does not write Automath paper or Lean content directly.

## Current Signal

- NewMath-to-Automath gate rows: `7`
- Killo/golden writeback-eligible rows: `1`
- Killo/golden review-blocked bridge sources: `1`
- PI actions: `4`

## Blocked Counts

| Reason | Count |
| --- | ---: |
| `awaiting_operator_acceptance` | 4 |
| `observe_only` | 2 |

## NewMath ACK Status Counts

| Status | Count |
| --- | ---: |
| `blocked` | 11 |
| `consumed` | 9 |
| `evidence_only` | 9 |

## Killo/Golden Review Blocks

| Source | Source Path |
| --- | --- |
| `NewMath bridge source: intro and carrier` | `papers/bedc/parts/concrete_instances/banach/intro_and_carrier.tex` |

## PI Actions

| Action | Effect | Severity |
| --- | --- | --- |
| `pi:automath:killo_golden_codex_fallback` | `use_codex_when_claude_unavailable` | `high` |
| `pi:automath:run_killo_golden_writeback` | `bridge_supervisor_may_apply_writeback_adapter` | `high` |
| `pi:automath:killo_golden_review_blocked` | `refine_bridge_source_context_and_retry` | `high` |
| `pi:automath:consume_newmath_ack_status` | `use_ack_reasons_to_adjust_next_scan` | `info` |

## Control Policy

- Automath writeback is allowed only through the native Killo/golden distillation lane.
- Claude unavailability is not a blocker when `review_backend=codex-claude`; Codex fallback remains within the same review prompts.
- Runtime candidate packets stay under `tools/automath_newmath_bridge/inbox/` and are not committed.
- Durable PI reports, ACK status, and receiving indexes are commit-worthy bridge telemetry.
