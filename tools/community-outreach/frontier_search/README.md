# Frontier Search Lane

This lane is for open-problem targets whose progress can be scored and verified
by finite artifacts: graphs, finite models, certificates, enumerations, SAT/ILP
witnesses, or reproducible computational records.

It is intentionally separate from prose-heavy outreach. A target enters this
lane only when its `science_contract.progress_metric` can be turned into a
machine score.

## Target Layout

```text
tools/community-outreach/frontier_search/targets/<slug>/
  target.yaml
  seed_bank/
  attempts/
  best/
  run_record.md
```

`target.yaml` fields:

```yaml
slug: example
title: Example finite search
score_command: ["python3", "score.py", "--artifact", "{artifact}"]
verify_command: ["python3", "verify.py", "--artifact", "{artifact}"]
lower_is_better: true
initial_artifact: seed_bank/seed.json
```

The score command must emit JSON:

```json
{"ok": true, "score": 12, "summary": "..."}
```

The verify command must emit JSON:

```json
{"ok": true, "verified": false, "summary": "..."}
```

The lane records `frontier_state.json` with the best artifact and attempt
history. It never sends external messages.
