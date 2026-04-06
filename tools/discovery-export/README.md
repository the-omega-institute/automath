# Discovery Export Tools

Extract theorem inventories from Lean 4 and create standalone paper repos.

## lean4_discovery_export.py

Parses all 10 Omega Lean 4 modules, extracts theorem/proof/docstring/labels,
generates ADR-008-v1 JSON.

```bash
python lean4_discovery_export.py              # Full export → discovery/discovery_report.json
python lean4_discovery_export.py --module Zeta # Single module
python lean4_discovery_export.py --stats       # Statistics only
python lean4_discovery_export.py --pretty      # Pretty-print JSON
```

Output schema per entry:

| Field | Description |
|-------|-------------|
| `discovery_id` | UUID5 (deterministic from module + name) |
| `lean_module` | e.g. `Omega.Zeta.DynZeta` |
| `lean_theorem` | Declaration name |
| `lean_type` | `theorem`, `lemma`, `def`, `abbrev`, `instance` |
| `lean_statement` | Type signature |
| `lean_proof` | Proof term or tactic block |
| `paper_labels` | Cross-reference labels (`prop:...`, `thm:...`) |
| `git_commit` | Latest commit touching the file |
| `git_date` | Date of that commit |

Output feeds into `notebooklm_pipeline.py` via `--discovery` flag.

## create_paper_repos.py

Create standalone GitHub repos for submitted papers under `the-omega-institute`.

```bash
python create_paper_repos.py --list            # Preview repo names
python create_paper_repos.py --all --dry-run   # Dry run
python create_paper_repos.py --all             # Create all repos
python create_paper_repos.py --paper <dir>     # Single paper
```

Each repo gets: source .tex/.bib, scripts, auto-generated README, .gitignore, MIT LICENSE.

## Requirements

- Python 3.8+ (stdlib only)
- `gh` CLI (for create_paper_repos.py)
- Git

## License

MIT
