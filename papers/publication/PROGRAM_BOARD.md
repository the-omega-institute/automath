# Publication Board

Updated: 2026-06-22

This board is for human tracking only: one paper or route per row. Machine
state, hard gates, temporary failures, and daemon scheduling details live in
`PROGRAM_BOARD_MACHINE.md`.

Current pipeline health: Oracle server is online and five ChatGPT Oracle tabs
are registered. The approved JDDE C+1 gate completed on 2026-06-11 with Oracle
`accept` and Codex `submit`. The remaining infrastructure task is to restart
the long-running supervisor under the Windows user environment that can execute
MiKTeX.

Operating rule: rejected routes have priority. If a rejected manuscript overlaps
strongly with a submitted or under-review manuscript, wait for the active
submission unless the board explicitly records a merge, supersession, or closure.

## Today

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| Pipeline daemon / Oracle | local automation | Oracle server online with 5 registered tabs. JDDE C+1 proved the Windows MiKTeX path works when the pipeline is launched under the real user environment. | Restart the long-running supervisor with `--parallel 5 --no-claude --no-auto-commit --no-server-spawn --no-pi-review`, then verify health snapshot and advancing logs. |
| `2026_auditable_theory_to_paper_pipeline` | CICM presentation-only / mathematical software workshop | Short-paper Oracle fresh review returned `Minor revision` with no two-page claim-boundary blocker. The requested packaging clarity was handled on 2026-06-21: short PDF clarifies roles versus coordinates, `CICM_SUPPLEMENT_README.md` names operative support records, and the supplement zip was rebuilt. | Ready for human EasyChair final check: verify author/order/metadata, visually inspect `submission_abstract.pdf`, confirm source link and supplement zip, then submit as CICM presentation-only. Do not run ordinary Stage B on `main.pdf` for this route. |

## Submitted: Wait For Feedback

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` | Journal of Theoretical Probability | Submitted; peer review in progress; 7 reviewers invited. Current title: "Exponential Tilting and Information Fluctuations for One-Step Markov Measures on Shifts of Finite Type". | Wait for editorial/reviewer feedback. Do not process overlapping zero-jitter route. |
| `submitted_2026_canonical_zeckendorf_normalization_berstel_adder_rairo_ita` | RAIRO-Theor. Inf. Appl. | Submitted; no feedback recorded. | Wait for result. |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | Journal of Number Theory | Submitted 2026-03-14; under review since 2026-03-25. Major revision completed and submitted; revision package recorded on `dev-automation-integration` commit `8f185f3a2`. Title: "A quartic cover of 37a1 and its regular S4-closure". | Wait for JNT feedback on the submitted major revision. |
| `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds` | DCDS-A | Submitted 2026-05-11; under review; Paper ID `260511-Zhang-2`. | Wait for result. Related Fibonacci/Zeckendorf finite-window manuscripts remain paused. |
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | Submitted; submission date and ID still need to be recorded. | Add submission ID/date when available. Old `prefix_scan_error...` route is legacy only. |
| `2026_homological_visibility_gluing_obstructions_state_forcing_apal` | APAL | Submitted manually by user on 2026-06-11. 2026-06-17: two referee-grade blockers fixed locally (§7.21 cocycle normalization; §7.14 Čech-site over-claim → precise finite-site Leray comparison), compiles clean — held as a revision-ready improvement, NOT re-entered. | Wait for APAL editorial feedback; use the 2026-06-17 fixes if a revision is requested. Do not process overlapping gluing-failure or recursive-addressing routes independently. |

## Ready Or Near-Ready After Human Review

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | JDDE | C-DONE after controlled C+1 on 2026-06-11. Round 16 returned Oracle `accept` and Codex `submit`, with 0 remaining work packages; no paper changes were needed. | Ready for human final submission review: confirm JDDE/Springer source-package requirements, author metadata, declarations, and upload files. |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Integral Equations and Operator Theory; backups: Operators and Matrices / Complex Analysis and Operator Theory | C-DONE after JST rejection. JST/EditFlow rejected as not suitable, with no technical referee report. Current retarget is IEOT, but research directive still calls for checking the Weyl-Horn singular-value body theorem package. | Not direct upload today. Verify the new Weyl-Horn package is actually in the manuscript, then final venue/package review. |
| `2026_elliptic_normalization_branch_geometry_quartic_spectral` | Indagationes Mathematicae | C-DONE, complete multi-file manuscript, split-overlap gate clean. No theorem-deepening blocker is recorded on the human board. | Do final theorem/venue review and Stage F journal confirmation; if no new blocker appears, prepare submission package. |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | Experimental Mathematics (was IMRN) | C-NEAR-PASS after retarget; recent Oracle accepted and Codex said submit, but this needs final human review / possible C+1 override rather than another ordinary rewrite loop. | Run `certificates/verify_certificates.py` under Sage and do final package/venue review before upload. |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | venue pending | C-DONE review history exists, but this is not yet a direct-upload route: the board lacks a concrete strengthened theorem package and venue decision. | Generate a theorem-deepening work order first, implement or explicitly reject it, then rerun Stage F/C after the strengthened package is present. |

## Active Rewrite / Retarget

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| _None_ | - | No ordinary rolling-pipeline paper is currently runnable. | Promote a paper into this section only after its board and machine gates are non-blocked. |

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
| `2026_detector_shells_click_record_kms_jphyscomm` | retarget physics-math venue | B-STUCK after 20 rounds: deepen review was minor revision but fresh Oracle returned reject, with blocker-level PDF/citation/bibliography/physics-claim issues. | Needs human decision: major repair, downgrade, or new route. Do not leave in rolling Active Rewrite until that decision is made. |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | retarget dynamical systems / symbolic dynamics venue | B-STUCK after the post-rejection reopen: Stage A passed on the Perron-boundary theorem spine, but the local machine board now records `deepen=?`, `fresh=?`, `20 rounds`, and `needs human review`. | Do not leave in rolling Active Rewrite. Decide whether this is an Oracle-infra reset/reopen, a manual B-stage review, or a venue/claim downgrade before allowing another automatic run. |
| `2026_single_primitive_universality_hierarchy` | Proc. AMS | Stage A blocked after repeated deterministic failure around Richardson normal-form obstruction and one-free-monogenic-orbit multiplication obstruction. | Needs real theorem strengthening or scope tightening before automatic rerun; avoid expanding into Zeckendorf/folded-family material. |
| `2026_prime_languages_finite_state_obstructions_monatshefte` | Monatshefte | C-SCOPE-STUCK after Stage C exhausted 15 rounds; ordinary rolling supervisor will not rerun it. | Needs explicit human override (`--extra-stage-c-rounds`) or a route decision: deep rewrite, merge, or lower/alternate venue. Do not process as ordinary Active Rewrite. |
| `2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` | ETDS | Parked; merged into folded-histograms route. | Use as material only. |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | legacy | Parked; canonical route is `2026_scan_error_prefix_partitions_convergence_rates_etds`. | Do not process independently. |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` / `2026_recursive_addressing_prefix_sites_tac` | APAL / TAC | Overlaps homological-visibility APAL route. | Decide canonical route before any work; currently APAL homological-visibility is canonical. |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | legacy | Duplicate of canonical JDDE route `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde`. | Do not process independently. |
| `2026_golden_ratio_driven_scan_projection_generation_recursive_emergence` | missing source | Board entry exists but local source directory is missing. | Do not process until source is restored or explicitly renamed. |

## Skeletons

| Paper or route | Venue | Status | Next step |
|---|---|---|---|
| `2026_group_unification_fibonacci_prime_window_entropy_time` | pending | Skeleton only. | Do not process now. |
| `2026_zeta_completion_xi_zero_audit` | pending | Skeleton only. | Do not process now. |
