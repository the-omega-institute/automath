# NewMath Supervisor Pattern Review

## Intake Status

This note is the durable Automath review packet for the only current
NewMath-to-Automath item admitted by the bridge selection gate:

| Field | Value |
| --- | --- |
| Source | `the-omega-institute/newmath@origin/auto-dev:tools/bedc-deep/supervisor.py` |
| Artifact kind | `pipeline_status` |
| Bridge readiness | `ready_for_local_packet` |
| Post-gate state | `awaiting_operator_acceptance` |
| Automath use | operational pattern review only |

The source is not paper content and is not a Lean theorem. It should not enter
Automath theory text, Lean files, or Killo/golden writeback as mathematical
content. Its value is that it describes a mature long-running production loop
whose control ideas can make the Automath-NewMath bridge more disciplined.

## Receivable Patterns

The NewMath BEDC supervisor separates a persistent outer loop from the workers
that perform theorem-site production. Automath should preserve that separation:
the bridge watchdog keeps the scanner, heavy synthesis loop, and production
loop alive, while each loop remains independently restartable. This lets an
operator update one bridge function without stopping all observation.

The low-water refill pattern is directly applicable. The bridge should treat an
empty or exhausted queue as a production signal, not as a reason to stop. When
no records are gate-passed, the correct next action is to refresh source refs,
rerun synthesis, and produce a blocked or review-only intake explanation. It is
not correct to manufacture acceptance.

The reject-cluster pattern is useful for quality control. Repeated failures
should be counted by reason category, such as missing receiving target,
synthesis-only evidence, non-packet destination, or operator-review boundary.
Those categories should affect priority before a candidate is polished. A
record repeatedly blocked for the same structural reason should be cooled down
until its missing receiving surface is supplied.

The loning-watch pattern is receivable as a monitoring surface. Automath can
observe NewMath branch movement, BEDC closure discipline, and bridge policy
changes without treating those observations as paper or Lean content. This is
especially useful when another machine has pushed fixes to the bridge branch.

The network-resume checkpoint pattern should be adapted cautiously. It is
appropriate for retrying a failed push of an already-created branch commit, but
not for converting runtime files into durable content. Automath bridge commits
should continue to exclude `inbox/`, `out/`, `state/`, `logs/`, and generated
review-packet JSON unless a later operator decision promotes a packet into a
durable source.

The periodic PI review pattern should remain advisory on the Automath side.
It can adjust cooldowns, priorities, and scan surfaces. It must not mark a
bridge item accepted, consumed, or Killo/golden-ready without the destination
gate that owns that kind of content.

## Local Adoption Contract

The Automath bridge can consume the supervisor pattern under the following
contract:

| Pattern | Local bridge use | Boundary |
| --- | --- | --- |
| Outer loop plus worker loops | Keep scanner, heavy synthesis, production, and watchdog loops separate | a worker restart is not content acceptance |
| Low-water refill | Trigger source refresh and synthesis when gate-passed output is empty | no synthetic writeback when gates are empty |
| Reject clustering | Classify repeated blocked reasons before priority selection | blocked records remain blocked |
| Loning watch | Observe remote pipeline and branch changes | observations do not become paper text |
| Network resume | Retry failed transport after a safe commit exists | runtime files remain uncommitted |
| PI review | Tune priorities and cooldowns | advisory only, no acceptance authority |

## Production Implication

The bridge already has the first layer of this pattern: a supervisor, a heavy
loop, a production loop, and a watchdog. The next useful Automath production
work is not another index refresh. It is to use the blocked-reason categories
as queue discipline:

- records with `blocked_automath_not_ready` wait for a named receiving theorem,
  article section, or Killo/golden target;
- records with `needs_operator_review` wait for an operator decision before
  any packet can become receivable;
- synthesis-only records may be summarized as review leads but cannot be
  selected for durable writeback;
- a gate-passed pipeline-status record may produce operational documentation,
  as this note does, but cannot produce mathematical prose.

This review packet therefore creates one meaningful Automath-side output from
the current NewMath gate pass: a reusable policy and operations intake note.
It deliberately does not create Automath paper content, because the selected
source is a pipeline supervisor rather than a mathematical result.
