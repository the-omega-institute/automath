# Next Steps

- [ ] Full blind run over all 175 residuals (currently only a 19-problem spike) -> produce `certs/blind_full_certs.jsonl` + `results/blind_full.json` + `manifests/blind_full_manifest.json` so the blind result becomes a benchmark.
- [ ] ATP baseline comparison (Twee / Vampire / Mace4) on the same residual sets -> the decisive experiment for whether the LLM layer adds value beyond existing provers.
- [ ] Distillation pass: mine the 173 certificates for a small set of reusable proof-template families / a decision procedure -> align with the competition's actual stated goal.
- [ ] Tighten replay: full `REPLAY_GUIDE.md` dry-run from a clean judge clone; confirm every manifest row re-verifies -> remove environment-dependent ambiguity.
- [ ] Extraction to a PRIVATE standalone repo (proposed name `fkst-sair-eqt2-escalation`); add LICENSE + CITATION.cff at that point -> prepare controlled external sharing.
- [ ] Paper framing memo -> arXiv-ready draft -> convert the internal method note into a publishable systems paper.
