# Honest Boundary

- Guided results (sample_200 200/200, hard2 198/200) are an UPPER BOUND: codex was given the ground-truth verdict.
- The blind result now covers the full 175 residuals (174/175 accepted, 0 wrong verdicts; only `hard2_0176` resists) -> blind sample_200 200/200, hard2 199/200. In blind mode codex is NOT given the ground-truth verdict; it searches for a finite counterexample and/or a universal proof and keeps whichever the Lean judge accepts, i.e. the judge is a solve-time oracle, not the answer key. Still a LOCAL-runner measurement, not a hosted-leaderboard submission.
- Scores come from a LOCAL clone of the official runner, NOT the hosted leaderboard.
- Nothing has been submitted or registered to any leaderboard.
- NO new mathematics: every problem has a known answer (the Equational Theories Project resolved all of them); certificates re-prove known facts.
- No claim that FKST "solves" SAIR.
- An external Lean judge checkout is required to reproduce; scripts depend on the Codex CLI and the local environment.
- Certificates are replayable only under the stated judge snapshot / proof policy (see manifests/judge_snapshot.json).
