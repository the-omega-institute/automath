import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete `Ξ_m` proxy with strictly smaller growth than `Γ_m`. -/
noncomputable def conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi
    (_m : ℕ) : ℝ :=
  1

/-- Concrete `Γ_m` proxy. -/
noncomputable def conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma
    (m : ℕ) : ℝ :=
  (m : ℝ) + 1

/-- Concrete `Σ_m` proxy with strictly larger growth than `Γ_m`. -/
noncomputable def conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Sigma
    (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) ^ 2

/-- A single renormalizing sequence would force all three normalized channels to converge to
nonzero finite constants. -/
def conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_commonRenormalization :
    Prop :=
  ∃ a : ℕ → ℝ, (∀ m, a m ≠ 0) ∧
    ∃ c1 c2 c3 : ℝ,
      c1 ≠ 0 ∧
      c2 ≠ 0 ∧
      c3 ≠ 0 ∧
      Tendsto
        (fun m =>
          conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi m / a m)
        atTop (𝓝 c1) ∧
      Tendsto
        (fun m =>
          conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma m / a m)
        atTop (𝓝 c2) ∧
      Tendsto
        (fun m =>
          conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Sigma m / a m)
        atTop (𝓝 c3)

lemma conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_ratio_tendsto_zero :
    Tendsto
      (fun m =>
        conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi m /
          conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma m)
      atTop
      (𝓝 0) := by
  have hshift : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
    simpa using
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  simpa
    [conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi,
      conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma, one_div] using
    (tendsto_inv_atTop_zero.comp hshift)

lemma conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_proof :
    ¬ conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_commonRenormalization :=
    by
  intro h
  rcases h with ⟨a, ha, c1, c2, c3, hc1, hc2, hc3, hXi, hGamma, _hSigma⟩
  have hratio :
      Tendsto
        (fun m =>
          (conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi m / a m) /
            (conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma m /
              a m))
        atTop
        (𝓝 (c1 / c2)) := by
    exact hXi.div hGamma hc2
  have hratio' :
      Tendsto
        (fun m =>
          conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi m /
            conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma m)
        atTop
        (𝓝 (c1 / c2)) := by
    convert hratio using 1
    funext m
    have hGamma_ne :
        conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma m ≠ 0 := by
      dsimp [conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma]
      positivity
    field_simp [ha m, hGamma_ne]
  have hzero :
      Tendsto
        (fun m =>
          conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Xi m /
            conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_Gamma m)
        atTop
        (𝓝 0) :=
    conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_ratio_tendsto_zero
  have hEq : c1 / c2 = 0 := tendsto_nhds_unique hratio' hzero
  exact (div_ne_zero hc1 hc2) hEq

/-- Paper label:
`prop:conclusion-binfold-gauge-complexity-no-single-parameter-renormalization`. -/
theorem paper_conclusion_binfold_gauge_complexity_no_single_parameter_renormalization :
    ¬ conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_commonRenormalization
    :=
  conclusion_binfold_gauge_complexity_no_single_parameter_renormalization_proof

end Omega.Conclusion
