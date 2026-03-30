# Publication Board

This is the single live board for publication operations.

## Program snapshot

| Paper | Target | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | Live status |
|---|---|---|---|---|---|---|---|---|---|---|
| APAL | Ann. Pure Appl. Logic | done | done | done | done | done | done | done | blocked | technical pack verified; waiting only on author metadata |
| ETDS | Ergodic Th. Dyn. Sys. | done | done | done | done | done | done | done | done | submission-ready once author metadata is inserted |
| TAMS | Trans. AMS | done | done | done | done | done | done | done | pending | P7 is the next real task |
| JFA | J. Funct. Anal. | done | done | done | pending | pending | pending | pending | pending | needs P5 proof polish and first live build |
| ETDS-zeta | Ergodic Th. Dyn. Sys. | done | done | done | done | done | pending | pending | pending | P4 accepted; move to P5 |

## Current wave

1. `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`
   - priority: `P5 -> P7`
   - next: integrate accepted P4 state, decide whether the `S_3` example needs
     a reproducibility note, then prepare the submission pack
   - blocker class: `metadata`, optional `reproducibility`
2. `2026_projection_ontological_mathematics_core_tams`
   - priority: `P7`
   - next: final clean PDF, submission checklist, cover-letter set, first
     upstream sync after theorem package freeze
   - blocker class: none internal to the math package
3. `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`
   - priority: `P5 -> P6`
   - next: compress `sec_precision_potential.tex`, apply bridging paragraphs,
     run first clean build, extract kernel theorem package
   - blocker class: `editorial`, `compile`
4. `2026_conservative_extension_chain_state_forcing_apal`
   - priority: `human unblock + P7 close`
   - next: wait for definitive author metadata, then rebuild and close P7
   - blocker class: `metadata`
5. `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`
   - priority: `hold`
   - next: no new agent work until author metadata or referee feedback appears
   - blocker class: `metadata`

## Open claims

- none at the moment; start from the current wave section above

## Next recommended claims

- `pub-integrator` -> `ETDS-zeta / P5 / main tex + TRACK_BOARD / next run`
- `pub-submission-pack` -> `TAMS / P7 / submission materials + final build / next run`
- `pub-proof-polish` -> `JFA / P5 / sec_precision_potential.tex + main.tex / next run`
- `pub-upstream-sync` -> `first stable P5/P7 track / sync notes + board update / next run`

## Completed handoffs

- `orchestrator` -> `APAL / P1 / SOURCE_MAP.md + THEOREM_LIST.md / next: research`
- `orchestrator` -> `ETDS / P1 / SOURCE_MAP.md + THEOREM_LIST.md / next: research`
- `orchestrator` -> `ETDS / P2 / P2_EXTENSION_NOTE_2026-03-30.md / next: rewrite`
- `orchestrator` -> `ETDS / P4 / P4_EDITORIAL_REVIEW_2026-03-30.md / next: integrator`
- `orchestrator` -> `TAMS / P1 / SOURCE_MAP.md + THEOREM_LIST.md / next: research`
- `pub-research` -> `APAL / P2 / P2_EXTENSION_NOTE_2026-03-30.md / next: rewrite` (2026-03-30)
- `pub-research` -> `TAMS / P2 / P2_EXTENSION_NOTE_2026-03-30.md / next: rewrite` (2026-03-30)
- `pub-journal-rewrite` -> `ETDS / P3 / P3_REWRITE_NOTE_2026-03-30.md + tex edits / next: integrator` (2026-03-30)
- `pub-lean-sync` -> `APAL / P6 / LEAN_SYNC_NOTE_2026-03-30.md / 0% verified` (2026-03-30)
- `pub-lean-sync` -> `ETDS / P6 / LEAN_SYNC_NOTE_2026-03-30.md / 0% verified, 27% partial` (2026-03-30)
- `pub-lean-sync` -> `TAMS / P6 / LEAN_SYNC_NOTE_2026-03-30.md / 25% verified, 31% partial` (2026-03-30)
- `Confucius` -> `APAL / P7 / P7_SUBMISSION_NOTE_2026-03-30.md + checklist and cover-letter hardening / next: human metadata or submission closer / local build: 37pp clean bib cycle` (2026-03-30)
- `Euler` -> `ETDS-zeta / P4 / P4_EDITORIAL_REVIEW_2026-03-30.md + sec_chebotarev.tex + sec_shadows.tex / next: integrator / local build: 36pp` (2026-03-30)

## Upstream and main-paper feedback

| Track | Upstream source roots | Required upstream feedback | Main-paper write-back | Child / sequel | Status |
|---|---|---|---|---|---|
| APAL | `logic_expansion_chain/` | four-layer packaging, forcing-necessity framing, contextuality bridge | rewrite canonical logic-expansion-chain narrative around the four-layer package | `K` observer-spacetime logic sequel | pending first upstream sync note |
| ETDS | `spg/` + `recursive_addressing/` | weighted-boundary transfer, open-system specialization, Poisson collision threshold, entropy-ledger phrasing | rewrite the SPG + recursive-addressing core around the ETDS theorem ladder | `F` depends directly | pending first upstream sync note |
| TAMS | `pom/` core + certified generated tables | principalization -> irreducibility -> full symmetric group -> linear disjointness -> product-density chain | rewrite the canonical POM arithmetic line to match the stabilized TAMS chain | arithmetic side branches later if stable | pending first upstream sync note |
| JFA | `circle_dimension_phase_gate/` | interface-theorem packaging, analytic bundle, portable section split for precision potential | rewrite the main-paper circle-dimension exposition around the interface/analytic split | `S4/Prym` remains separate | pending first upstream sync note |
| ETDS-zeta | `zeta_finite_part/{syntax,online_kernel,operator,finite_part}` | finite-part chain as a single explicit theorem ladder, keep `xi/` out of parent-line main claims | rewrite the main-paper zeta finite-part chapter to foreground the stabilized finite-part ladder | `H1`, `H2`, `H3`, `J` remain child candidates | pending first upstream sync note |

## Shared Lean core status

| Track | P6 status | Current core status | Meaning | Next core wave |
|---|---|---|---|---|
| APAL | complete | `0/13 verified`, no direct core counterparts yet | manuscript may proceed, theorem package remains backlog-level in the shared core | create a kernel target list for the four-layer chain |
| ETDS | complete | `0 verified`, `27% partial` (`4/15`) | submission is allowed, but claims still need extraction into core-library tasks | prioritize sigma-nonexpansion core and transfer theorem package |
| TAMS | complete | `4/16 verified`, `5/16 partial` | strongest current bridge into the shared core library | push transfer, Gibbs-selection, arithmetic-window core claims |
| JFA | pending | one simplified partial match only; no stable core package yet | no formalization gate yet because the theorem package is not frozen | wait for P5 proof polish, then extract the final kernel package |
| ETDS-zeta | pending | no durable paper-local P6 record yet | paper can continue editorially, but the core target is still undefined | after P5, extract a strict theorem list and classify the finite-part core |

## Board update rule

When an agent starts work:

- claim ownership in this file under `Open claims`

When an agent finishes work:

- move the claim to `Completed handoffs`
- update the affected program snapshot row if stage status changed
- update upstream or formalization sections if the output touched those lanes
