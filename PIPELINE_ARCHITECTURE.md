# Pipeline Architecture

## Model

The outreach oracle uses `chatgpt-5.5-pro` by default. The browser userscript does not pin a model; it relays the model name supplied by the local outreach oracle server.

## Author / Editor Split

The oracle is the paper author for breakthrough outreach runs. Codex is not allowed to synthesize the paper from a transcript after the fact.

Codex's role begins after the oracle has written a full LaTeX document:

- polish bibliography and references;
- normalize standalone structure against `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/main.tex`;
- enforce the outreach backflow language policy for standalone papers: English only, no Chinese prose;
- preserve oracle-authored theorem statements and proof strategy unless a concrete edit is needed.

## Flow

1. `dispatch_worktree.py --oracle-deep` starts the multi-turn `deep_reasoning` loop.
2. `DEFAULT_DEEPENING_PROMPTS` drives follow-up turns until the oracle reaches `BREAKTHROUGH`, `STUCK`, `FAILED`, or `EXHAUSTED`.
3. If `--write-latex` is set and the final verdict is `BREAKTHROUGH`, the pipeline sends one terminal `WRITE_PAPER_LATEX` prompt in the same oracle conversation.
4. The oracle returns one full self-contained LaTeX paper plus a plain forum summary.
5. `oracle_consultant.extract_latex_from_response()` extracts either a fenced `latex` block or a bare `\documentclass` document.
6. The LaTeX is saved to `theory/2026_outreach_<slug>/main.tex`.
7. The deep-run record persists `latex_path` and `plain_summary` in `tools/community-outreach/outreach_state/<slug>.json`.
8. Codex runs only as editor/polisher through `generate_outreach_paper(<latex_path>)`, invoking `/opt/homebrew/bin/codex exec` to edit `main.tex` in place.
9. The polished paper can then enter the normal `oracle_pipeline.py` P0-P7 paper pipeline and PDF build path.

## Non-Goals

- No automatic commit or push.
- No external forum, email, PR, or issue submission without explicit user approval.
- No Codex-authored replacement paper when the oracle LaTeX is missing or empty; that is a hard error.
