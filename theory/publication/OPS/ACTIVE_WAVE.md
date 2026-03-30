# Active Wave

This board is the live dispatch queue for parallel publication agents.

## Wave 3 priorities

### 1. `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`

- Priority: `P5 -> P7`
- Why now:
  P4 is now accepted after a real editorial pass and a fresh local build.
- Immediate deliverables:
  - integrate the P4 conclusions as the accepted paper state
  - decide whether the `S_3` example needs a paper-local reproducibility note
  - prepare the ETDS submission pack after metadata is ready
- Current blocker class:
  `metadata` for final submission, `reproducibility` for the optional `S_3`
  support note

### 2. `2026_projection_ontological_mathematics_core_tams`

- Priority: `P7`
- Why now:
  P5 and P6 are complete; this is the strongest track that can still gain a
  concrete submission-pack upgrade without new mathematics.
- Immediate deliverables:
  - compile a clean final PDF
  - produce the TAMS submission checklist and cover-letter set
  - confirm theorem-chain and appendix package are frozen
  - write the first paper-local upstream sync note once the package is frozen
- Current blocker class:
  none inside the math package; remaining work is submission-pack assembly

### 3. `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`

- Priority: `P5 -> P6`
- Why now:
  P1 and P2 are done, but this track still needs proof polish and a real build
  before it becomes submission-credible.
- Immediate deliverables:
  - split or compress `sec_precision_potential.tex`
  - add the targeted bridging and optimality paragraphs from P2
  - run the first clean live build
  - extract the theorem package that will eventually drive P6
- Current blocker class:
  `editorial` and `compile`

### 4. `2026_conservative_extension_chain_state_forcing_apal`

- Priority: `human unblock + P7 close`
- Why now:
  the technical submission pack is already hardened; only author metadata keeps
  the paper from a true submission-ready state.
- Immediate deliverables:
  - wait for definitive author metadata
  - once supplied, insert it, rebuild, and close P7
- Current blocker class:
  `metadata`

### 5. `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`

- Priority: `hold`
- Why now:
  this track is already submission-ready apart from human-supplied author
  metadata.
- Immediate deliverables:
  - no new agent work until author metadata is available or referee feedback
    arrives
- Current blocker class:
  `metadata`

## Suggested lane assignment if 6 to 10 agents are available

- Agent 1: orchestrator and claims board
- Agent 2: ETDS-zeta integrator / reproducibility note
- Agent 3: TAMS submission-pack agent
- Agent 4: JFA proof-polish agent
- Agent 5: JFA compile-and-bib agent
- Agent 6: APAL submission closer once author metadata exists
- Agent 7: ETDS metadata closer once author metadata exists
- Agent 8: Lean sync / backlog extraction on the most advanced open track
- Agent 9: upstream sync agent for any track that completes a stable P5/P7 state
- Agent 10: bibliography / recent-paper recon only when a live target changes
- Agent 11: editorial review reserve for any track that finishes a rewrite pass

## Wave completion criterion

Wave 3 is done when:

- ETDS-zeta is through P5 with its remaining risks explicitly classified
- TAMS has a real P7 pack
- at least one new paper-local upstream sync note exists
- JFA has completed both P5 and its first live build
- APAL and ETDS remain clearly marked as waiting only on human metadata
