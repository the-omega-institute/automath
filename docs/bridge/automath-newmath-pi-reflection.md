# Automath-NewMath PI Reflection

This report is the deterministic PI layer for the NewMath-to-Automath bridge.
It turns global bridge and ACK signals into disciplined Killo/golden writeback control actions.
It does not write Automath paper or Lean content directly.

## Current Signal

- NewMath-to-Automath gate rows: `9`
- Killo/golden writeback-eligible rows: `0`
- Killo/golden review-blocked bridge sources: `0`
- PI actions: `3`

## Blocked Counts

| Reason | Count |
| --- | ---: |
| `awaiting_operator_acceptance` | 7 |
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
| _none_ | _none_ |

## PI Actions

| Action | Effect | Severity |
| --- | --- | --- |
| `pi:automath:killo_golden_codex_fallback` | `use_codex_when_claude_unavailable` | `high` |
| `pi:automath:no_eligible_writeback` | `continue_scanning_and_wait_for_accepted_or_consumed_rows` | `medium` |
| `pi:automath:consume_newmath_ack_status` | `use_ack_reasons_to_adjust_next_scan` | `info` |

## Control Policy

- Automath writeback is allowed only through the native Killo/golden distillation lane.
- Claude unavailability is not a blocker when `review_backend=codex-claude`; Codex fallback remains within the same review prompts.
- Runtime candidate packets stay under `tools/automath_newmath_bridge/inbox/` and are not committed.
- Durable PI reports, ACK status, and receiving indexes are commit-worthy bridge telemetry.
