import Mathlib.Tactic
import Omega.Conclusion.M2Level3Incidence24IdentificationKillMinus4
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys
import Omega.Conclusion.M2Level3XiInertiaHeckeEigensystemsCharpoly

namespace Omega.Conclusion

/-- Concrete wrapper datum for the audited order-`6` flag-local-system splitting package. -/
structure conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_data where
  conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_witness : Unit := ()

/-- The common summand is the image `QQ ⊕ V24` of the incidence map. -/
abbrev conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_common_block :=
  conclusion_m2_level3_incidence_24_identification_kill_minus4_image_Phi

/-- Klingen-side defect summand. -/
abbrev conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_klingen_block :=
  conclusion_m2_level3_incidence_24_identification_kill_minus4_ker_Phi

/-- Siegel-side defect summand. -/
abbrev conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_siegel_block :=
  conclusion_m2_level3_incidence_24_identification_kill_minus4_coker_Phi

/-- Rank of the common `QQ ⊕ V24` block. -/
def conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_common_rank : ℕ :=
  1 + 24

/-- Rank of the Klingen defect block. -/
def conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_klingen_rank : ℕ := 15

/-- Rank of the Siegel defect block. -/
def conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_siegel_rank : ℕ := 15

/-- Rank of the order-`6` flag local system obtained from the audited edge/vertex exact sequence. -/
def conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_steinberg_rank : ℕ :=
  120 - 40 + 1

/-- Characteristic polynomial of the audited order-`6` flag local system. -/
noncomputable def conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_steinberg_charpoly :
    Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_St

/-- Concrete paper-facing formulation of the order-`6` orthogonal splitting wrapper. -/
def conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_statement
    (_D : conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_data) : Prop :=
  conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_steinberg_rank = 81 ∧
    conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_steinberg_charpoly =
      conclusion_m2_level3_xi_delta0_order6_charpolys_St ∧
    conclusion_m2_level3_incidence_24_identification_kill_minus4_ker_Phi =
      conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_klingen_block ∧
    Nonempty
      (conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_siegel_block ≃
        conclusion_m2_level3_incidence_24_identification_kill_minus4_V15_Si) ∧
    conclusion_m2_level3_incidence_24_identification_kill_minus4_image_Phi =
      conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_common_block ∧
    Nonempty
      (conclusion_m2_level3_incidence_24_identification_kill_minus4_V24_Kl ≃
        conclusion_m2_level3_incidence_24_identification_kill_minus4_V24_Si) ∧
    conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_common_rank = 25 ∧
    conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_klingen_rank = 15 ∧
    conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_siegel_rank = 15 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Kl =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 5 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 4 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Si =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 3 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 4 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2 ∧
    conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Kl = 8 ∧
    conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Si = 4 ∧
    conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Kl ≠
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Si

/-- Paper label: `thm:conclusion-m2-level3-flag-local-system-orthogonal-splitting-order6`. -/
theorem paper_conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6
    (D : conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_data) :
    conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_statement D := by
  rcases paper_conclusion_m2_level3_incidence_24_identification_kill_minus4 with
    ⟨_, _, hker, hcoker, himage, hV24⟩
  rcases paper_conclusion_m2_level3_xi_delta0_order6_charpolys (D := ⟨()⟩) with
    ⟨_, _, _, _, hV15KlChar, hV15SiChar, _, _, _⟩
  rcases paper_conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly with
    ⟨_, _, _, _, _, _, hminusKl, _, hminusSi, _, _, _⟩
  refine ⟨?_, rfl, hker, hcoker, himage, hV24, ?_, rfl, rfl, hV15KlChar, hV15SiChar,
    hminusKl, hminusSi, ?_⟩
  · norm_num [conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_steinberg_rank]
  · norm_num [conclusion_m2_level3_flag_local_system_orthogonal_splitting_order6_common_rank]
  · norm_num [hminusKl, hminusSi]

end Omega.Conclusion
