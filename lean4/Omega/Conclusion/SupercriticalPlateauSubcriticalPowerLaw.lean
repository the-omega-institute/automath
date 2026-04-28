import Mathlib.Tactic

namespace Omega.Conclusion

/-- The golden-ratio atom scale appearing in the two-atom limiting curve. -/
noncomputable def conclusion_supercritical_plateau_subcritical_power_law_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The `q = 2` leading coefficient before simplifying the golden-ratio algebra. -/
noncomputable def conclusion_supercritical_plateau_subcritical_power_law_twoAtomCoeffQ2 : ℝ :=
  (conclusion_supercritical_plateau_subcritical_power_law_phi +
      conclusion_supercritical_plateau_subcritical_power_law_phi⁻¹ ^ 2) / Real.sqrt 5

/-- The paper's endpoint curve, restricted to the exact plateau and the leading
two-atom subcritical branch needed for the formal statement. -/
noncomputable def conclusion_supercritical_plateau_subcritical_power_law_energyQ2
    (τ : ℝ) : ℝ :=
  if 1 ≤ τ then
    1
  else
    conclusion_supercritical_plateau_subcritical_power_law_twoAtomCoeffQ2 * τ⁻¹

lemma conclusion_supercritical_plateau_subcritical_power_law_phi_sq :
    conclusion_supercritical_plateau_subcritical_power_law_phi ^ 2 =
      conclusion_supercritical_plateau_subcritical_power_law_phi + 1 := by
  unfold conclusion_supercritical_plateau_subcritical_power_law_phi
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hsqrt_sq]
  ring

lemma conclusion_supercritical_plateau_subcritical_power_law_phi_pos :
    0 < conclusion_supercritical_plateau_subcritical_power_law_phi := by
  unfold conclusion_supercritical_plateau_subcritical_power_law_phi
  positivity

lemma conclusion_supercritical_plateau_subcritical_power_law_twoAtomCoeffQ2_eq :
    conclusion_supercritical_plateau_subcritical_power_law_twoAtomCoeffQ2 =
      2 / Real.sqrt 5 := by
  have hsq := conclusion_supercritical_plateau_subcritical_power_law_phi_sq
  have hne :
      conclusion_supercritical_plateau_subcritical_power_law_phi ≠ 0 :=
    ne_of_gt conclusion_supercritical_plateau_subcritical_power_law_phi_pos
  unfold conclusion_supercritical_plateau_subcritical_power_law_twoAtomCoeffQ2
  field_simp [hne]
  nlinarith

/-- Concrete plateau/subcritical-power-law statement for the verified paper theorem. -/
def conclusion_supercritical_plateau_subcritical_power_law_statement : Prop :=
  (∀ τ : ℝ,
      1 ≤ τ →
        conclusion_supercritical_plateau_subcritical_power_law_energyQ2 τ = 1) ∧
    ∀ τ : ℝ,
      τ < 1 →
        conclusion_supercritical_plateau_subcritical_power_law_energyQ2 τ =
          (2 / Real.sqrt 5) * τ⁻¹

/-- Paper label: `thm:conclusion-supercritical-plateau-subcritical-power-law`. -/
theorem paper_conclusion_supercritical_plateau_subcritical_power_law :
    conclusion_supercritical_plateau_subcritical_power_law_statement := by
  constructor
  · intro τ hτ
    simp [conclusion_supercritical_plateau_subcritical_power_law_energyQ2, hτ]
  · intro τ hτ
    have hnot : ¬1 ≤ τ := not_le.mpr hτ
    simp [
      conclusion_supercritical_plateau_subcritical_power_law_energyQ2,
      hnot,
      conclusion_supercritical_plateau_subcritical_power_law_twoAtomCoeffQ2_eq,
    ]

end Omega.Conclusion
