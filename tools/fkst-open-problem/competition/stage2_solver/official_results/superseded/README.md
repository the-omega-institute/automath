# Superseded official-runner snapshots

These JSON files are broken/superseded intermediate official-runner snapshots preserved
only as audit evidence. They are **not authoritative**; use the current result files
listed in `../README.md` under "Which file is the truth" for score evidence.

| file | reason non-authoritative |
|---|---|
| `sample200_no-pydontwritebytecode_156.json` | sample_200 run was broken because it ran without `PYTHONDONTWRITEBYTECODE`. |
| `hard2_arithmetic-op_DISALLOWED_23.json` | hard2 arithmetic-op attempt was broken because it hit `DISALLOWED_DECLARATIONS`. |
| `hard1_partial69_17.json` | hard1 run covered only a partial problem set and was never finalized. |

These byte records cannot be re-derived because the local Lean judge environment in
`/tmp` was purged. See `../../SUBSTRATE_NOTES.md` for the full regression-and-fix story.
