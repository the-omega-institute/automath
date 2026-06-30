# SAIR-EQT2 24-Hour FKST Runbook

This runbook is for the focused SAIR-EQT2 dogfood supervisor. It uses the
`omega-sair-eqt2` package, not the broader `omega-open-problem` package.

## Boundary

- Target: `SAIR-EQT2` only.
- GitHub writes: disabled unless explicitly approved.
- Mathematical truth: Lean/checker/source-replay/git artifacts only.
- FKST consensus: routing state only.

## Start Real Consensus Run

This starts real FKST consensus. It may spawn Codex subprocesses from the
`consensus.decide` department. That means proposal context and referenced repo
content may be sent to the configured Codex backend. Start this only after the
operator explicitly approves that risk.

In this execution environment, plain `nohup ... &` did not survive the shell
session. Use the LaunchAgent path below for the actual 24-hour run.

```sh
cat > /tmp/org.omega.fkst-sair-eqt2.plist <<'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"
  "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key>
  <string>org.omega.fkst-sair-eqt2</string>
  <key>ProgramArguments</key>
  <array>
    <string>/tmp/fkst-substrate/target/debug/fkst-framework</string>
    <string>supervise</string>
    <string>--project-root</string>
    <string>/tmp/fkst-sair-eqt2-composed</string>
    <string>--framework-bin</string>
    <string>/tmp/fkst-substrate/target/debug/fkst-framework</string>
    <string>--package-root</string>
    <string>/tmp/fkst-sair-eqt2-composed/packages/consensus</string>
    <string>--package-root</string>
    <string>/tmp/fkst-sair-eqt2-composed/packages/omega-sair-eqt2</string>
  </array>
  <key>EnvironmentVariables</key>
  <dict>
    <key>PATH</key>
    <string>/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin</string>
    <key>FKST_RUNTIME_ROOT</key>
    <string>/tmp/fkst-sair-eqt2-runtime</string>
    <key>FKST_DURABLE_ROOT</key>
    <string>/tmp/fkst-sair-eqt2-durable</string>
    <key>FKST_RATE_POOL_ROOT</key>
    <string>/tmp/fkst-sair-eqt2-rate-pools</string>
    <key>FKST_GITHUB_WRITE</key>
    <string>0</string>
  </dict>
  <key>WorkingDirectory</key>
  <string>/Users/lexa/Desktop/lexa/omega/automath-outreach</string>
  <key>StandardOutPath</key>
  <string>/tmp/fkst-sair-eqt2-supervise.log</string>
  <key>StandardErrorPath</key>
  <string>/tmp/fkst-sair-eqt2-supervise.err</string>
  <key>RunAtLoad</key>
  <true/>
</dict>
</plist>
PLIST

mkdir -p /tmp/fkst-sair-eqt2-composed/packages
ln -sfn /tmp/fkst-packages/packages/consensus \
  /tmp/fkst-sair-eqt2-composed/packages/consensus
ln -sfn "$PWD/tools/fkst-open-problem/packages/omega-sair-eqt2" \
  /tmp/fkst-sair-eqt2-composed/packages/omega-sair-eqt2

launchctl bootout "gui/$(id -u)" org.omega.fkst-sair-eqt2 >/dev/null 2>&1 || true
launchctl bootstrap "gui/$(id -u)" /tmp/org.omega.fkst-sair-eqt2.plist
launchctl kickstart -k "gui/$(id -u)/org.omega.fkst-sair-eqt2"
```

Fallback if running in a shell that preserves background jobs:

```sh
mkdir -p /tmp/fkst-sair-eqt2-composed/packages
ln -sfn /tmp/fkst-packages/packages/consensus \
  /tmp/fkst-sair-eqt2-composed/packages/consensus
ln -sfn "$PWD/tools/fkst-open-problem/packages/omega-sair-eqt2" \
  /tmp/fkst-sair-eqt2-composed/packages/omega-sair-eqt2

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

echo $! > /tmp/fkst-sair-eqt2-supervise.pid
```

## Safe Preflight

These commands do not start a 24-hour external Codex consensus run:

```sh
python3 tools/fkst-open-problem/scripts/check_seed.py

/tmp/fkst-substrate/target/debug/fkst-framework test \
  --project-root tools/fkst-open-problem/packages/omega-sair-eqt2 \
  --package-root tools/fkst-open-problem/packages/omega-sair-eqt2 \
  --report-json /tmp/omega-sair-eqt2-fkst-test.actual.json

/tmp/fkst-substrate/target/debug/fkst-framework conformance \
  --project-root /tmp/fkst-sair-eqt2-composed \
  --package-root /tmp/fkst-sair-eqt2-composed/packages/consensus \
  --package-root /tmp/fkst-sair-eqt2-composed/packages/omega-sair-eqt2
```

## Check

```sh
launchctl print "gui/$(id -u)/org.omega.fkst-sair-eqt2"
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py \
  --append-jsonl /tmp/fkst-sair-eqt2-health.jsonl
python3 tools/fkst-open-problem/scripts/sair_eqt2_watch_once.py
python3 tools/fkst-open-problem/scripts/sair_eqt2_ledger_audit.py
tail -n 120 /tmp/fkst-sair-eqt2-supervise.log
tail -n 80 /tmp/fkst-sair-eqt2-supervise.err
rg -n 'dead_letter|DEAD_LETTER|framework failed|raised publish error|DRY_RUN_REPO_ARTIFACT|fkst-converge-diagnostic' \
  /tmp/fkst-sair-eqt2-runtime/logs /tmp/fkst-sair-eqt2-supervise.log
```

## 30-Minute Patrol

The patrol job simulates a recurring operator check every 30 minutes. It
records health, ledger continuity, dry-run artifact agreement, target boundary
quality, and runtime error patterns.

Boundaries:

- It is SAIR-EQT2-only.
- It keeps GitHub writes disabled.
- It may kickstart the SAIR-EQT2 supervisor if health/ledger checks fail.
- It may regenerate `claim_state.jsonl` from the deterministic SAIR-EQT2 dry-run
  if the committed artifact drifts from the generator.
- It does not edit source code, commit changes, push, or file upstream issues.
- FKST upstream issues are written as local candidates only until the user
  explicitly confirms filing.

Install or refresh the LaunchAgent:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_patrol.py \
  --install-launchagent \
  --interval-seconds 1800
```

Run once manually:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_patrol.py --once-json
```

Inspect status and output:

```sh
launchctl print "gui/$(id -u)/org.omega.fkst-sair-eqt2-patrol"
tail -n 20 tools/fkst-open-problem/artifacts/sair-eqt2/patrol_log.jsonl
cat tools/fkst-open-problem/artifacts/sair-eqt2/patrol_report.md
cat tools/fkst-open-problem/artifacts/sair-eqt2/fkst_issue_candidates.jsonl 2>/dev/null || true
tail -n 80 /tmp/fkst-sair-eqt2-patrol.log
tail -n 80 /tmp/fkst-sair-eqt2-patrol.err
```

Stop the patrol job:

```sh
launchctl bootout "gui/$(id -u)" /tmp/org.omega.fkst-sair-eqt2-patrol.plist
```

Optional health watcher for a 24-hour run:

```sh
cat > /tmp/org.omega.fkst-sair-eqt2-watch.plist <<'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"
  "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key>
  <string>org.omega.fkst-sair-eqt2-watch</string>
  <key>ProgramArguments</key>
  <array>
    <string>/opt/homebrew/bin/python3</string>
    <string>/Users/lexa/Desktop/lexa/omega/automath-outreach/tools/fkst-open-problem/scripts/sair_eqt2_watch_once.py</string>
    <string>--jsonl</string>
    <string>/tmp/fkst-sair-eqt2-health.jsonl</string>
  </array>
  <key>WorkingDirectory</key>
  <string>/Users/lexa/Desktop/lexa/omega/automath-outreach</string>
  <key>StandardOutPath</key>
  <string>/tmp/fkst-sair-eqt2-watch.log</string>
  <key>StandardErrorPath</key>
  <string>/tmp/fkst-sair-eqt2-watch.err</string>
  <key>StartInterval</key>
  <integer>900</integer>
  <key>RunAtLoad</key>
  <true/>
</dict>
</plist>
PLIST

launchctl bootout "gui/$(id -u)" \
  /tmp/org.omega.fkst-sair-eqt2-watch.plist >/dev/null 2>&1 || true
launchctl bootstrap "gui/$(id -u)" \
  /tmp/org.omega.fkst-sair-eqt2-watch.plist
launchctl print "gui/$(id -u)/org.omega.fkst-sair-eqt2-watch"
```

Expected startup should include:

```text
dept=omega-sair-eqt2.seed_sair_stage2
dept=omega-sair-eqt2.converge_diagnostic
dept=omega-sair-eqt2.repo_artifact_sink
raiser=omega-sair-eqt2.sair_stage2
FKST_GITHUB_WRITE => 0
DRY_RUN_REPO_ARTIFACT
```

It must not include:

```text
seed_t43
omega-open-problem.seed
```

After 24 hours, use the same health check with an age requirement:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py \
  --min-age-seconds 86400
python3 tools/fkst-open-problem/scripts/sair_eqt2_health_check.py \
  --min-age-seconds 86400 \
  --append-jsonl /tmp/fkst-sair-eqt2-health.jsonl
python3 tools/fkst-open-problem/scripts/sair_eqt2_watch_once.py \
  --min-age-seconds 86400
python3 tools/fkst-open-problem/scripts/sair_eqt2_ledger_audit.py \
  --min-age-seconds 86400 \
  --min-samples 24 \
  --max-gap-seconds 1800 \
  --max-staleness-seconds 1800 \
  --max-first-age-seconds 1800
python3 tools/fkst-open-problem/scripts/sair_eqt2_ledger_audit.py \
  --min-age-seconds 86400 \
  --min-samples 24 \
  --max-gap-seconds 1800 \
  --max-staleness-seconds 1800 \
  --max-first-age-seconds 1800 \
  --json
python3 tools/fkst-open-problem/scripts/sair_eqt2_status_report.py \
  --final-24h \
  --append-current \
  --json \
  --output /tmp/fkst-sair-eqt2-final-status.json
```

## Stop

```sh
launchctl bootout "gui/$(id -u)" /tmp/org.omega.fkst-sair-eqt2.plist
launchctl bootout "gui/$(id -u)" /tmp/org.omega.fkst-sair-eqt2-watch.plist
```
