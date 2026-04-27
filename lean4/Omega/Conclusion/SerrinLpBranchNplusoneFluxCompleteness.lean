import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite decoder data for a centered diagonal `l_p` Serrin/Wulff branch. -/
structure conclusion_serrin_lp_branch_nplusone_flux_completeness_data where
  conclusion_serrin_lp_branch_nplusone_flux_completeness_dimension : ℕ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_p : ℕ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_axis_power : Fin
    conclusion_serrin_lp_branch_nplusone_flux_completeness_dimension → ℚ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_zeroth_flux : ℚ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_coordinate_flux : Fin
    conclusion_serrin_lp_branch_nplusone_flux_completeness_dimension → ℚ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_domain_code : ℕ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_decoded_domain_code : ℕ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_certificate_count : ℕ
  conclusion_serrin_lp_branch_nplusone_flux_completeness_centered : Bool
  conclusion_serrin_lp_branch_nplusone_flux_completeness_p_gt_one :
    1 < conclusion_serrin_lp_branch_nplusone_flux_completeness_p
  conclusion_serrin_lp_branch_nplusone_flux_completeness_zeroth_flux_ne_zero :
    conclusion_serrin_lp_branch_nplusone_flux_completeness_zeroth_flux ≠ 0
  conclusion_serrin_lp_branch_nplusone_flux_completeness_coordinate_flux_eq :
    ∀ i,
      conclusion_serrin_lp_branch_nplusone_flux_completeness_coordinate_flux i =
        conclusion_serrin_lp_branch_nplusone_flux_completeness_axis_power i *
          conclusion_serrin_lp_branch_nplusone_flux_completeness_zeroth_flux
  conclusion_serrin_lp_branch_nplusone_flux_completeness_centered_eq :
    conclusion_serrin_lp_branch_nplusone_flux_completeness_centered = true
  conclusion_serrin_lp_branch_nplusone_flux_completeness_domain_decode_eq :
    conclusion_serrin_lp_branch_nplusone_flux_completeness_decoded_domain_code =
      conclusion_serrin_lp_branch_nplusone_flux_completeness_domain_code
  conclusion_serrin_lp_branch_nplusone_flux_completeness_certificate_count_eq :
    conclusion_serrin_lp_branch_nplusone_flux_completeness_certificate_count =
      conclusion_serrin_lp_branch_nplusone_flux_completeness_dimension + 1

/-- Axis-power recovery from the zeroth flux and the coordinate fluxes. -/
def conclusion_serrin_lp_branch_nplusone_flux_completeness_decoded_axis_power
    (D : conclusion_serrin_lp_branch_nplusone_flux_completeness_data)
    (i : Fin D.conclusion_serrin_lp_branch_nplusone_flux_completeness_dimension) : ℚ :=
  D.conclusion_serrin_lp_branch_nplusone_flux_completeness_coordinate_flux i /
    D.conclusion_serrin_lp_branch_nplusone_flux_completeness_zeroth_flux

namespace conclusion_serrin_lp_branch_nplusone_flux_completeness_data

/-- The centered diagonal branch is uniquely decoded from `n + 1` scalar fluxes. -/
def claim (D : conclusion_serrin_lp_branch_nplusone_flux_completeness_data) : Prop :=
  (∀ i,
      conclusion_serrin_lp_branch_nplusone_flux_completeness_decoded_axis_power D i =
        D.conclusion_serrin_lp_branch_nplusone_flux_completeness_axis_power i) ∧
    D.conclusion_serrin_lp_branch_nplusone_flux_completeness_decoded_domain_code =
      D.conclusion_serrin_lp_branch_nplusone_flux_completeness_domain_code ∧
      D.conclusion_serrin_lp_branch_nplusone_flux_completeness_certificate_count =
        D.conclusion_serrin_lp_branch_nplusone_flux_completeness_dimension + 1

end conclusion_serrin_lp_branch_nplusone_flux_completeness_data

/-- Paper label: `thm:conclusion-serrin-lp-branch-nplusone-flux-completeness`. -/
theorem paper_conclusion_serrin_lp_branch_nplusone_flux_completeness
    (D : conclusion_serrin_lp_branch_nplusone_flux_completeness_data) : D.claim := by
  unfold conclusion_serrin_lp_branch_nplusone_flux_completeness_data.claim
  refine ⟨?_, D.conclusion_serrin_lp_branch_nplusone_flux_completeness_domain_decode_eq,
    D.conclusion_serrin_lp_branch_nplusone_flux_completeness_certificate_count_eq⟩
  intro i
  unfold conclusion_serrin_lp_branch_nplusone_flux_completeness_decoded_axis_power
  rw [D.conclusion_serrin_lp_branch_nplusone_flux_completeness_coordinate_flux_eq i]
  field_simp [D.conclusion_serrin_lp_branch_nplusone_flux_completeness_zeroth_flux_ne_zero]

end Omega.Conclusion
