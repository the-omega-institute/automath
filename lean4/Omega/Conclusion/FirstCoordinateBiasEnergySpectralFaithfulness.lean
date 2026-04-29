import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-first-coordinate-bias-energy-spectral-faithfulness`. -/
theorem paper_conclusion_first_coordinate_bias_energy_spectral_faithfulness {ι : Type*}
    [Fintype ι] (ν : ι → ℝ) (uniform collision : Prop)
    (huniform : uniform ↔ ∀ r, ν r = 0) (hcollision : collision ↔ ∀ r, ν r = 0) :
    ((∑ r, ν r ^ 2 = 0) ↔ uniform) ∧ ((∑ r, ν r ^ 2 = 0) ↔ collision) := by
  have henergy : (∑ r, ν r ^ 2 = 0) ↔ ∀ r, ν r = 0 := by
    constructor
    · intro hsum r
      have hfun : (fun r => ν r ^ 2) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg fun r => sq_nonneg (ν r)).mp hsum
      have hterm : ν r ^ 2 = 0 := by
        simpa using congr_fun hfun r
      exact sq_eq_zero_iff.mp hterm
    · intro hzero
      simp [hzero]
  exact ⟨henergy.trans huniform.symm, henergy.trans hcollision.symm⟩

end Omega.Conclusion
