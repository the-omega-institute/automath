# Publication Board

Updated: 2026-07-13

This board is for human tracking only: one paper or route per row. Machine
state, hard gates, temporary failures, and daemon scheduling details live in
`PROGRAM_BOARD_MACHINE.md`.

Current pipeline health: the local NyxID `chatgpt-pro` CDP pool is the
scheduler target for this branch, with three local tabs. The WSL supervisor
runs the rolling paper pipeline with `--parallel 3`; shared `omega-oracle` is
not the scheduler target for this branch.

Operating rule: rejected routes have priority. If a rejected manuscript overlaps
strongly with a submitted or under-review manuscript, wait for the active
submission unless the board explicitly records a merge, supersession, or closure.

## Today

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| Pipeline daemon / Oracle | local automation | Local NyxID `chatgpt-pro` CDP pool online with 3 registered tabs. The long-running supervisor is running under WSL with `--parallel 3 --no-auto-commit --no-server-spawn --no-pi-review`; `.inner.restart` has been reissued so the next safe drain loads the active batch-checkpoint fix. | Keep the local 3-tab pool as the scheduler target; do not use the shared `omega-oracle` pool for this branch's rolling paper pipeline. |

## Submitted: Wait For Feedback

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` | Journal of Theoretical Probability | Submitted to JTP; peer review in progress. | Wait for editorial/reviewer feedback. Recorded context: 7 reviewers invited; current title "Exponential Tilting and Information Fluctuations for One-Step Markov Measures on Shifts of Finite Type". Do not process overlapping zero-jitter route. |
| `submitted_2026_canonical_zeckendorf_normalization_berstel_adder_rairo_ita` | RAIRO-Theor. Inf. Appl. | Referee reports received; major revision package finalized and independently reviewed as submission-ready. Manuscript `ITA-2026-0032`. | Upload `ITA-2026-0032_manuscript.pdf`, `ITA-2026-0032_source.zip`, and `ITA-2026-0032_response_to_referees.pdf` through the RAIRO portal. Record the revision submission date and status after portal confirmation; do not reopen theorem development or rerun the paper pipeline. |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | Journal of Number Theory | Submitted to JNT 2026-03-14; under review since 2026-03-25; major revision submitted. | Wait for JNT feedback on the submitted major revision. Recorded context: revision package on `dev-automation-integration` commit `8f185f3a2`; title "A quartic cover of 37a1 and its regular S4-closure". |
| `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds` | DCDS-A | Rejected by DCDS-A (Paper ID `260511-Zhang-2`); editor suggested Electronic Research Archive / AIMS Math. Math not faulted (scope/fit). | Do not resend to DCDS. Deepen before retarget: prove the metallic/β-family threshold classification `m*(β)`, then submit to ERA / AIMS Math / ETDS. Related Fibonacci/Zeckendorf finite-window manuscripts remain paused. |
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | Submitted; submission date and ID still need to be recorded. | Add submission ID/date when available. Old `prefix_scan_error...` route is legacy only. |
| `2026_homological_visibility_gluing_obstructions_state_forcing_apal` | APAL | **REJECTED** 2026-08 (Manuscript `APAL-D-26-00107`, editor Benno van den Berg). Submitted 2026-06-11. The rejection was **not on content**: the editor wrote that the manuscript "does not meet the standard requirements for a mathematical paper in terms of style", "uses terminology in a way that is not standard and is not explained", and that consequently "an evaluation of its content is not possible in its current state". No referee assessed the mathematics. Structural facts behind this: 93 pages, 52 definitions, 81 theorems/propositions, and heavy custom vocabulary that collides with standard usage — `realization` 198x (a standard model-theory term used here for something else), `slice` 133x (collides with slice category), `visible`/`visibility` 223x, `admitted reference` 42x, `bouquet` 19x. Earlier 2026-06-17 fixes (§7.21 cocycle normalization; §7.14 Cech-site over-claim → finite-site Leray comparison) are still held locally. | **Do not shop it to another journal — the same desk rejection follows anywhere.** Fix presentation first: (1) terminology audit, rename terms that collide with standard logic/category usage, add a glossary mapping each coined term to its standard counterpart; (2) compress 93pp to 35-45pp with a compiled supplement, using the method already validated on A2/A4/A7; (3) lead the introduction with the crisp result (a nonzero finite abelian G occurs as a pure two-branch resolution kernel exactly when d(G) <= 2*beta and G is not a cyclic p-group) stated in standard language, instead of burying it. Then re-target: APAL again (citing the rewrite), or JSL / Logic and Analysis / Theory and Applications of Categories. Independent tier assessment is running. |
| `2026_auditable_theory_to_paper_pipeline` | CICM 2026 Presentation Only | Accepted to CICM 2026 (Presentation Only). Submission `3974`; paper `CICM_2026_paper_3974.pdf`; title "Publication-Coordinate Audit Interfaces for AI-Assisted Formal-Mathematics Pipelines". | Prepare presentation; confirm any camera-ready/scheduling requirements with the chairs. |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | Journal of Dynamics and Differential Equations | Rejected by JDDE. Result is geometric analysis (sharp `1/(2k)` homotopy bound + box calibration), no dynamics content — venue mismatch. Duplicate route `cubical_stokes_...jdsgt` shares ~70% of it. | Do not resend as-is. Either drop, or fold into a single geometric-analysis note and target a geometric-analysis venue, not a dynamics journal. |

## Ready Or Near-Ready After Human Review

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Integral Equations and Operator Theory; backups: Operators and Matrices / Complex Analysis and Operator Theory | JST/EditFlow rejected as not suitable; retargeted to IEOT. | Not direct upload today. Pipeline checkpoint: C-DONE/ready-needs-human-review after JST rejection. Verify the new Weyl-Horn package is actually in the manuscript, then final venue/package review. |

## Active Rewrite / Retarget

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `2026_detector_shells_click_record_kms_jphyscomm` | retarget physics-math venue | GRG and JPhysComm rejected; canonical route is retargeting. | Still active. Latest machine state 2026-07-06 11:32: Stage B reopened at B1, but Oracle infra paused after three no-valid-response attempts. Next automatic action is re-submit the same B1 review when local Oracle capacity is clear; do not move to ready/submitted. |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | retarget dynamical systems / symbolic dynamics venue | ETDS rejected; route reopened for dynamical/symbolic-dynamics retarget. | Still active. Latest machine state 2026-07-06 11:25: Stage B is at B5/B6 after ETDS rejection, last deepen verdict minor revision, but Oracle infra paused at B6. Next automatic action is retry B6 with a clean fresh Oracle review. |
| `2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa` | JFA / analysis venue | Targeting JFA/analysis venue; no submission result recorded. | Still active. Latest machine state 2026-07-06 13:22: Stage C reached C5, last recorded final verdict lane was `oracle:minor revision;claude:revise`, then Oracle final-review retry paused on invalid/no response. Next automatic action is rerun C5 final gate. |
| `2026_prime_languages_finite_state_obstructions_monatshefte` | Monatshefte | Targeting Monatshefte; no submission result recorded. | Still active. Do not downgrade because the last Stage A escalation produced no paper diff: that is treated as NyxID/Oracle extraction or instruction-capture failure, not evidence that no research route exists. Latest machine state 2026-07-06 14:12: A-BLOCKED score=4 after repeated unparseable/no-change escalation cycles. Next action is rerun Oracle escalation after NyxID capture is fixed, requiring concrete theorem/venue instructions. |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | Experimental Mathematics (was IMRN) | IMRN route retargeted to Experimental Mathematics; not yet submitted to T&F. | Still active but blocked on Oracle capacity, not ready for Taylor & Francis upload. Latest machine state 2026-07-06 13:22: Stage C C1 re-submit hit NyxID `oracle_quota_exceeded` / invalid final-review response; retry C1 after local pool clears. |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | venue pending | Venue not selected; no submission result recorded. | In active rewrite now. Latest log 2026-07-06 13:43-14:13: Stage B round 2 deepen was minor revision, fresh eval returned major revision, repeated blocker is Theorem 3.11; Codex focused fixes B4.1-B4.3 are being applied to the manuscript/source files. Keep running targeted rewrite and then rerun B review. |

## Newmath Intake

These are not active papers until manually promoted into a `2026_*` directory.

| Seed | Priority | Status | Next step |
|---|---:|---|---|
| `newmath_intake/seeds/bedc_automation_pipeline` | P0 | Promoted to active track `2026_auditable_theory_to_paper_pipeline`; seed is archive/source packet only. | Continue in active paper directory; do not process seed independently. |
| `newmath_intake/seeds/bedc_finite_kernel_calculus` | P0 | Exact statements read; blocker ledger, related-work scaffold, and short-note memo prepared. Current theorem spine is too local for direct journal promotion. | Add or identify an upstream packaging theorem, or explicitly choose a modest workshop/short-note route. |
| `newmath_intake/seeds/bedc_rule110_finite_witness` | P0 | Static recheck found count drift; local machine lacks required build toolchain for full rerun. Trust-chain template and diagnostic route memo prepared. | Install/use build toolchain, rerun full suite, then resolve count/collision-audit contradictions before promotion. |
| `newmath_intake/seeds/metacic_closed_normal_consistency` | P1 | Intake-ready MetaCIC type-theory note candidate. | Related-work audit and exact theorem boundary. |
| `newmath_intake/seeds/observer_state_semantics` | P1 | Intake-ready observer-state semantics candidate. | Reframe as workshop/position paper; avoid strong AI-consciousness claims. |

## Parked / Overlap / Do Not Process Independently

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `submitted_2026_finite_window_rigidity_fibonacci_numeration_fq` | Fibonacci Quarterly | Rejected 2026-05-01. Local decision: highly overlaps DCDS-A paper `260511-Zhang-2`. | Do not retarget independently. Wait for DCDS-A feedback. |
| `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj` / `2026_upper_fibers_witness_covers_fibonacci_apparition_fq` | Ramanujan J. / Fibonacci Quarterly | RJ rejected for insufficient novelty/repackaging and an `n=30`/eight-types data issue. FQ route remains blocked by overlap with submitted/current sibling routes. | Only revive if we add substantive arithmetic content and fix the data issue; otherwise wait/merge. |
| `2026_folded_histograms_sampling_certificates_parry_mismatch_etds` | ETDS / symbolic dynamics venue | Hard Stage A block: semantic overlap requires explicit board resolution before this paper can advance. SIADS rejected for application-fit; canonical merge/retarget route is not yet board-resolved. | Do not run in the rolling pipeline until the board explicitly closes, supersedes, merges, or reopens the overlapping folded-histograms route. |
| `submitted_2026_folded_histograms_sampling_certificates_parry_mismatch_siads` | SIADS | Rejected; merged into canonical folded-histograms ETDS route. | Do not process independently. |
| `submitted_2026_folded_rotation_histogram_etds` | ETDS | Same rejected folded-histograms/SIADS route family. | Do not process independently. |
| `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt` | Journal of Number Theory | Rejected; superseded by DCDS-A `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds`. | Do not process while DCDS-A is under review. |
| `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp` | Journal of Theoretical Probability | Rejected; superseded by tilt-dynamics JTP route. | Do not process while JTP route is under review. |
| `submitted_2026_shell_geometry_detector_thermality_kms_grg` | GRG | Rejected history route; superseded by canonical detector-shells rewrite. | Do not process independently; use as background for detector-shells. |
| `2026_single_primitive_universality_hierarchy` | Proc. AMS | Stage A blocked after repeated deterministic failure around Richardson normal-form obstruction and one-free-monogenic-orbit multiplication obstruction. | Needs real theorem strengthening or scope tightening before automatic rerun; avoid expanding into Zeckendorf/folded-family material. |
| `2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` | ETDS | Parked; merged into folded-histograms route. | Use as material only. |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | legacy | Parked; canonical route is `2026_scan_error_prefix_partitions_convergence_rates_etds`. | Do not process independently. |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` / `2026_recursive_addressing_prefix_sites_tac` | APAL / TAC | Overlaps homological-visibility APAL route. | Decide canonical route before any work; currently APAL homological-visibility is canonical. |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | legacy | Duplicate of canonical JDDE route `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde`. | Do not process independently. |
| `2026_golden_ratio_driven_scan_projection_generation_recursive_emergence` | missing source | Board entry exists but local source directory is missing. | Do not process until source is restored or explicitly renamed. |
| `2026_elliptic_normalization_branch_geometry_quartic_spectral` | Indagationes Mathematicae | Parked before journal upload: Indagationes author guide requires papers to be uploaded to arXiv before journal consideration; no local arXiv ID is recorded. The manuscript is otherwise complete as a multi-file PDF/source package. | First prepare and submit the arXiv package, then reopen the Indagationes journal submission route after an arXiv identifier is available. |

## Skeletons

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `2026_group_unification_fibonacci_prime_window_entropy_time` | pending | Skeleton only. | Do not process now. |
| `2026_zeta_completion_xi_zero_audit` | pending | Skeleton only. | Do not process now. |
