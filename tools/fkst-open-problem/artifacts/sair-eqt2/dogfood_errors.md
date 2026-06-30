# SAIR-EQT2 FKST Dogfood Error Log

This file records FKST runtime issues found while dogfooding the SAIR-EQT2
pipeline. These are automation/runtime findings, not mathematical facts.

## 2026-06-15: Single-package `run` cannot raise cross-package queue

Command shape:

```sh
/tmp/fkst-substrate/target/debug/fkst-framework run \
  tools/fkst-open-problem/packages/omega-open-problem/departments/proposal_intake/main.lua \
  --project-root tools/fkst-open-problem/packages/omega-open-problem \
  --package-root tools/fkst-open-problem/packages/omega-open-problem \
  --event '{"queue":"omega_proposal", ...}'
```

Observed error:

```text
qualified name `consensus.proposal` uses namespace `consensus` but legacy owner namespace is `omega-open-problem`
```

Impact:

- `proposal_intake` can be tested in the FKST unit-test harness.
- Production `run` requires a composed project root when raising to
  `consensus.proposal`.

Resolution:

- Run cross-package SAIR-EQT2 departments under a composed project root.
- Pass `--owner-namespace omega-open-problem` or use a package whose namespace
  matches the focused graph.

## 2026-06-15: Existing composed graph is too broad for SAIR-only dogfood

Command shape:

```sh
env FKST_GITHUB_WRITE=0 \
  /tmp/fkst-substrate/target/debug/fkst-framework supervise \
  --project-root /tmp/fkst-omega-composed \
  --framework-bin /tmp/fkst-substrate/target/debug/fkst-framework \
  --package-root /tmp/fkst-omega-composed/packages/consensus \
  --package-root /tmp/fkst-omega-composed/packages/omega-open-problem
```

Observed startup:

```text
dept=omega-open-problem.seed_t43 consumer started
raiser=omega-open-problem.seed cron raiser starting
raiser=omega-open-problem.sair_stage2 cron raiser starting
```

Impact:

- The graph starts successfully.
- It violates the SAIR-EQT2-only dogfood boundary because old open-problem
  routes are loaded.

Resolution:

- Use a separate `omega-sair-eqt2` package for the 24-hour run.
- The focused package must contain only SAIR-EQT2 departments and raisers.

## 2026-06-15: Sandbox blocks real consensus angle subprocesses

Command shape:

```sh
env FKST_RUNTIME_ROOT=/tmp/fkst-sair-eqt2-runtime-smoke \
  FKST_DURABLE_ROOT=/tmp/fkst-sair-eqt2-durable-smoke \
  FKST_RATE_POOL_ROOT=/tmp/fkst-sair-eqt2-rate-pools-smoke \
  FKST_GITHUB_WRITE=0 \
  timeout 5 /tmp/fkst-substrate/target/debug/fkst-framework supervise \
    --project-root /tmp/fkst-sair-eqt2-composed \
    --framework-bin /tmp/fkst-substrate/target/debug/fkst-framework \
    --package-root /tmp/fkst-sair-eqt2-composed/packages/consensus \
    --package-root /tmp/fkst-sair-eqt2-composed/packages/omega-sair-eqt2
```

Observed error in `consensus.decide` child log:

```text
consensus dept=decide tag=FAILURE error_class=caught-failure
queue=consensus.proposal error=Operation not permitted (os error 1)
stack traceback: [C]: in function 'await_all'
```

Context:

- The focused graph started correctly.
- The graph loaded only `omega-sair-eqt2` and `consensus`.
- The failure happened after judgment worktree creation, when consensus tried
  to await spawned Codex angle processes.

Impact:

- Short smoke runs inside the restricted sandbox can verify graph shape and
  pre-consensus delivery.
- A real consensus run must be started outside the sandbox so FKST can spawn
  Codex subprocesses.

Resolution:

- Start the 24-hour dogfood supervisor with approved escalated execution.
- Keep `FKST_GITHUB_WRITE=0`.

## 2026-06-15: 24-hour real consensus run requires explicit risk approval

Attempted command shape:

```sh
env FKST_RUNTIME_ROOT=/tmp/fkst-sair-eqt2-runtime \
  FKST_DURABLE_ROOT=/tmp/fkst-sair-eqt2-durable \
  FKST_RATE_POOL_ROOT=/tmp/fkst-sair-eqt2-rate-pools \
  FKST_GITHUB_WRITE=0 \
  nohup /tmp/fkst-substrate/target/debug/fkst-framework supervise \
    --project-root /tmp/fkst-sair-eqt2-composed \
    --framework-bin /tmp/fkst-substrate/target/debug/fkst-framework \
    --package-root /tmp/fkst-sair-eqt2-composed/packages/consensus \
    --package-root /tmp/fkst-sair-eqt2-composed/packages/omega-sair-eqt2 \
    > /tmp/fkst-sair-eqt2-supervise.log 2>&1 &
```

Observed approval-system rejection:

```text
Starting the 24-hour supervisor would launch real Codex consensus subprocesses
against repo data outside the sandbox, which risks sending private workspace
content to an unverified external service.
```

Impact:

- The 24-hour real consensus supervisor was not started.
- Do not bypass this with indirect shell execution, wrapper scripts, or a
  different process launcher.

Resolution:

- Real 24-hour consensus run requires explicit operator approval after this
  risk is acknowledged.
- Until then, use static checks, package tests, conformance, composed `run`
  steps with synthetic consensus, and short sandbox smoke runs.

## 2026-06-16: Plain background supervisor did not survive the shell session

Command shape:

```sh
env FKST_RUNTIME_ROOT=/tmp/fkst-sair-eqt2-runtime \
  FKST_DURABLE_ROOT=/tmp/fkst-sair-eqt2-durable \
  FKST_RATE_POOL_ROOT=/tmp/fkst-sair-eqt2-rate-pools \
  FKST_GITHUB_WRITE=0 \
  nohup /tmp/fkst-substrate/target/debug/fkst-framework supervise ... &
```

Observed behavior:

- The supervisor could be launched interactively.
- It did not remain a reliable 24-hour process after the shell session ended.

Impact:

- `nohup ... &` is not the preferred real-run path in this environment.

Resolution:

- Use the documented `org.omega.fkst-sair-eqt2` LaunchAgent.
- Keep stdout/stderr in `/tmp/fkst-sair-eqt2-supervise.log` and
  `/tmp/fkst-sair-eqt2-supervise.err`.

## 2026-06-16: Consensus convergence output had no SAIR consumer

Observed supervisor log:

```text
consensus.decide ... delivery acked
queue consensus.consensus_converge has no delivery subscriptions
```

Context:

- The first approved real run loaded only `consensus` and `omega-sair-eqt2`.
- `consensus.decide` produced `consensus.consensus_converge` rather than
  `consensus.consensus_reached`.

Impact:

- A non-final consensus decision retried toward dead letter.
- Retrying the same convergence diagnostic would not improve mathematical
  evidence and would make the 24-hour run noisy.

Resolution:

- Add `omega-sair-eqt2.converge_diagnostic`.
- Consume `consensus.consensus_converge`.
- Emit a diagnostic `omega_artifact_task` that explicitly says it is not a
  mathematical claim.

## 2026-06-16: Dry-run repo artifact queue had no terminal consumer

Observed supervisor log:

```text
raised publish error: queue omega-sair-eqt2.omega_repo_artifact has no delivery subscriptions
```

Context:

- `artifact_writer` correctly produced an `omega.repo_artifact.v1` payload.
- `FKST_GITHUB_WRITE=0` was set, so no GitHub or repo write should happen.
- The graph still needs a terminal consumer so delivery can be acknowledged.

Impact:

- The supervisor retried the already-rendered repo artifact.
- A 24-hour run would accumulate retries even though the pipeline had reached
  its dry-run boundary.

Resolution:

- Add `omega-sair-eqt2.repo_artifact_sink`.
- Consume `omega_repo_artifact`, produce nothing, and log
  `DRY_RUN_REPO_ARTIFACT`.
- Keep `github_write=false`; the sink records runtime quality only and does
  not write GitHub or repository files.

## 2026-06-16: Focused artifact namespace drifted from package namespace

Observed artifact:

```text
fkst_proposal_id=omega-open-problem/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4
```

Context:

- The focused runtime package now uses `omega-sair-eqt2`.
- The first committed claim-state artifact still carried the older broader
  `omega-open-problem` proposal namespace.

Impact:

- The dry-run comparison could pass while the durable artifact identity did not
  match the focused package used by the 24-hour supervisor.

Resolution:

- Update `claim_state.jsonl` and `sair_eqt2_dry_run.py` to use
  `omega-sair-eqt2/SAIR-EQT2/...`.
- Re-run dry-run comparison and FKST package tests.

## 2026-06-16: Health check could not rely on `ps` in the sandbox

Command:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py
```

Observed error:

```text
PermissionError: [Errno 1] Operation not permitted: 'ps'
```

Context:

- The LaunchAgent was running.
- The first health-check implementation tried to call `ps -p <pid> -o etime=`
  to measure process age.

Impact:

- The 24-hour run could be healthy while the health check failed in the same
  restricted environment used for FKST dogfood monitoring.

Resolution:

- Keep using `launchctl print` for service state and PID.
- Measure runtime age from the last `event runtime running` timestamp in
  `/tmp/fkst-sair-eqt2-supervise.log`.
- Preserve `--min-age-seconds 86400` for final 24-hour verification.

## 2026-06-16: Health check required artifact body text that the sink does not log

Command:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py
```

Observed error:

```text
convergence diagnostic artifact was not observed
```

Context:

- Runtime logs showed `consensus.consensus_converge` delivered to
  `converge_diagnostic`, then `artifact_writer`, then `repo_artifact_sink`.
- The sink intentionally logs artifact metadata and `content_bytes`, not the
  full artifact body.

Impact:

- The health check produced a false negative.
- Requiring full artifact text in runtime logs would also make logs noisier
  without improving mathematical evidence.

Resolution:

- Validate the durable event chain instead:
  `consensus.consensus_converge -> converge_diagnostic ->
  omega_artifact_task -> artifact_writer -> omega_repo_artifact ->
  repo_artifact_sink`.
- Continue requiring `DRY_RUN_REPO_ARTIFACT` and `github_write=false`.

## 2026-06-16: Successful health snapshots alone do not record failed checks

Command shape:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py \
  --append-jsonl /tmp/fkst-sair-eqt2-health.jsonl
```

Observed limitation:

- The command appends a health record after all checks pass.
- If the health check fails, the process exits before appending a structured
  error record.

Impact:

- A 24-hour dogfood run could have only terminal output for a failed monitor
  sample.
- That is weaker than the goal of saving FKST dogfood errors for later audit.

Resolution:

- Add `sair_eqt2_watch_once.py`.
- It runs the health check once, appends `omega.sair_eqt2.health.v1` on
  success, and appends `omega.sair_eqt2.health_error.v1` with stdout/stderr
  snippets on failure.
- Keep this wrapper SAIR-EQT2-only; it does not supervise general FKST jobs or
  write GitHub state.

## 2026-06-16: Health check could pass from stale pre-restart evidence

Observed risk:

- The supervisor stdout can contain multiple runtime segments after
  `launchctl kickstart` or a process restart.
- A health check that searches the whole log can find an old
  `repo_artifact_sink` ack even if the current runtime segment has not yet
  closed its first cycle.

Impact:

- A restarted 24-hour run could be reported healthy before the new instance
  reaches the dry-run sink.
- This would weaken the final `--min-age-seconds 86400` evidence.

Resolution:

- Make `sair_eqt2_health_check.py` locate the last
  `MSG=event runtime running` line.
- Require startup, department, ack, and runtime evidence in the current segment
  or in child logs modified after that runtime start.
- Keep old log scanning only for forbidden error text that should fail the
  audit if it appears in the current run's runtime files.

Follow-up:

- The first segment fix still included complete stdout/stderr in the forbidden
  text scan.
- That could make a past failed runtime segment fail a current healthy segment,
  or make current-run evidence harder to reason about.
- The health check now builds current runtime text from the current stdout
  segment, stderr lines at or after current runtime start, and child logs
  modified at or after current runtime start.

## 2026-06-16: Health snapshots need a final ledger audit

Observed limitation:

- Individual `sair_eqt2_watch_once.py` samples prove point-in-time health.
- They do not by themselves prove that the JSONL has enough samples, no error
  rows, monotonic runtime age, stable target, and acceptable sampling gaps.

Impact:

- A 24-hour claim could be made from one final health sample while ignoring
  a mid-run error row or a long monitoring gap.

Resolution:

- Add `sair_eqt2_ledger_audit.py`.
- It reads `/tmp/fkst-sair-eqt2-health.jsonl`, rejects
  `omega.sair_eqt2.health_error.v1` rows, checks SAIR-EQT2-only fields,
  checks monotonic `checked_at` and `runtime_age_seconds`, and supports final
  gates such as `--min-age-seconds 86400 --min-samples 24
  --max-gap-seconds 1800`.
- It also supports `--json` for a machine-readable final report with schema
  `omega.sair_eqt2.ledger_audit.v1`.

Follow-up:

- A ledger with no errors can still be stale if the watcher stopped writing
  samples.
- Add `--max-staleness-seconds` so final 24-hour audit can require the last
  JSONL sample to be recent.
- A ledger can also start too late and still have enough final samples if it is
  backfilled or sampled too densely near the end.
- Add `--max-first-age-seconds` so the final audit can require monitoring to
  have started near the beginning of the runtime.

Follow-up:

- An ad hoc check used `--max-gap-seconds 300`, but the watcher interval is
  900 seconds.
- That made the ledger audit fail on healthy watcher cadence.
- Use `--max-gap-seconds 1800` for the 24-hour runbook and combined status
  report.

## 2026-06-16: Final readiness needed a single combined status command

Observed limitation:

- Health check, ledger audit, and final 24-hour gates were separate commands.
- It was easy to inspect a passing current health check while missing that the
  ledger was not yet old or dense enough for final 24-hour completion.

Impact:

- Operators could confuse "currently healthy" with "24-hour objective
  complete".

Resolution:

- Add `sair_eqt2_status_report.py`.
- Default mode reports current SAIR-EQT2 health plus ledger status.
- `--final-24h` runs the 86400-second and sample-count gates and reports
  `not_ready` until both health and ledger audits pass.
- It supports `--output` so the final JSON status can be written to
  `/tmp/fkst-sair-eqt2-final-status.json`.

Follow-up:

- The first status report read the ledger as-is.
- At final 24-hour time, the watcher might not have written a very recent
  sample yet.
- Add `--append-current` so the report can first append a current health sample
  to the ledger, then audit that ledger. If the current health gate fails, it
  records `append_error` and does not append a false-success sample.
- The status report now also includes a `gates` object so the JSON artifact
  records the thresholds used to decide `ok` or `not_ready`.

## 2026-06-16: Python syntax checks wrote disallowed `__pycache__`

Command shape:

```sh
python3 -m py_compile tools/fkst-open-problem/scripts/sair_eqt2_*.py
```

Observed error:

```text
PermissionError: [Errno 1] Operation not permitted: '.../scripts/__pycache__'
```

Context:

- Adding syntax checks for the SAIR-EQT2 monitoring scripts is useful because
  the final 24-hour proof depends on those scripts running at the end.
- Plain `py_compile` writes bytecode into the repository by default.

Impact:

- A good syntax check could fail for filesystem reasons unrelated to the
  pipeline.

Resolution:

- `check_seed.py` now compiles SAIR-EQT2 Python scripts with explicit `cfile`
  paths under a temporary directory.
- This checks syntax without writing `__pycache__` into the repository.

## 2026-06-16: Status JSON could disagree with append-current failure

Observed risk:

- `sair_eqt2_status_report.py --append-current` runs a health append first,
  then runs health and ledger checks for the report.
- The first implementation returned a non-zero process exit when append failed,
  but the JSON `status` field only considered the later health and ledger
  results.

Impact:

- A final 24-hour report could be machine-read as `ok` while still carrying a
  non-null `append_error` and exiting non-zero.
- That is confusing for the final gate because the status artifact should agree
  with the command result.

Resolution:

- Include `append_error is None` in the status calculation.
- Keep `append_error` in the JSON so a failed final append remains auditable.
