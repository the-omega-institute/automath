import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

set_option linter.unusedVariables false

/-- Paper label: `cor:conclusion-physical-temperature-golden-bernoulli-cumulant-law`. -/
theorem paper_conclusion_physical_temperature_golden_bernoulli_cumulant_law :
    let phi : ℝ := (1 + Real.sqrt 5) / 2
    let L : ℝ := Real.log phi
    let p : ℝ := 1 / (1 + phi ^ 2)
    p = 1 / (phi * Real.sqrt 5) ∧ p = 1 / 2 - Real.sqrt 5 / 10 ∧
      p * (1 - p) = 1 / 5 ∧
      p * (1 - p) * (1 - 2 * p) = Real.sqrt 5 / 25 ∧
      p * (1 - p) * (1 - 6 * p * (1 - p)) = -1 / 25 := by
  let phi : ℝ := (1 + Real.sqrt 5) / 2
  let p : ℝ := 1 / (1 + phi ^ 2)
  change p = 1 / (phi * Real.sqrt 5) ∧ p = 1 / 2 - Real.sqrt 5 / 10 ∧
    p * (1 - p) = 1 / 5 ∧
    p * (1 - p) * (1 - 2 * p) = Real.sqrt 5 / 25 ∧
    p * (1 - p) * (1 - 6 * p * (1 - p)) = -1 / 25
  set r : ℝ := Real.sqrt 5
  have hr2 : r ^ 2 = 5 := by
    rw [show r = Real.sqrt 5 by rfl]
    norm_num
  have hr_pos : 0 < r := by
    rw [show r = Real.sqrt 5 by rfl]
    positivity
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hphi_def : phi = (1 + r) / 2 := by rfl
  have hphi_sq : phi ^ 2 = phi + 1 := by
    rw [hphi_def]
    field_simp
    ring_nf
    nlinarith
  have hone_phi_sq : 1 + phi ^ 2 = phi * r := by
    rw [hphi_sq, hphi_def]
    field_simp
    ring_nf
    nlinarith
  have hp_eq : p = 1 / (phi * r) := by
    rw [show p = 1 / (1 + phi ^ 2) by rfl, hone_phi_sq]
  have hp_closed : p = 1 / 2 - r / 10 := by
    rw [hp_eq, hphi_def]
    field_simp [hr_ne]
    ring_nf
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [show r = Real.sqrt 5 by rfl] using hp_eq
  · simpa [show r = Real.sqrt 5 by rfl] using hp_closed
  · rw [hp_closed]
    field_simp
    ring_nf
    nlinarith
  · rw [hp_closed]
    field_simp
    ring_nf
    nlinarith
  · rw [hp_closed]
    field_simp
    ring_nf
    nlinarith

end

end Omega.Conclusion
