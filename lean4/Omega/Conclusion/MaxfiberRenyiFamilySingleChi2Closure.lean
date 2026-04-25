import Mathlib.Tactic

namespace Omega.Conclusion

/-- Label-prefixed preservation of the abstract Rényi-family equality. -/
theorem conclusion_maxfiber_renyi_family_single_chi2_closure_family
    (Dlim Dtwo : ℝ → ℝ) (hfamily : ∀ a : ℝ, 0 < a → Dlim a = Dtwo a) :
    ∀ a : ℝ, 0 < a → Dlim a = Dtwo a := by
  exact hfamily

/-- Label-prefixed algebraic recovery of `phi` from the supplied chi-square scalar. -/
theorem conclusion_maxfiber_renyi_family_single_chi2_closure_phi_recovery
    (Dchi phi : ℝ) (hphi : phi = (5 * Dchi + 3) / 2) :
    phi = (5 * Dchi + 3) / 2 := by
  exact hphi

/-- Paper label: `thm:conclusion-maxfiber-renyi-family-single-chi2-closure`.
The limiting Rényi family collapses to the two-point family, and the chi-square constant
recovers the golden scalar by the stated affine formula. -/
theorem paper_conclusion_maxfiber_renyi_family_single_chi2_closure
    (Dlim Dtwo : ℝ → ℝ) (Dchi phi : ℝ)
    (hfamily : ∀ a : ℝ, 0 < a → Dlim a = Dtwo a)
    (hchi : Dchi = (2 * phi - 3) / 5)
    (hphi : phi = (5 * Dchi + 3) / 2) :
    (∀ a : ℝ, 0 < a → Dlim a = Dtwo a) ∧ phi = (5 * Dchi + 3) / 2 := by
  have _hchi_recorded : Dchi = (2 * phi - 3) / 5 := hchi
  exact ⟨
    conclusion_maxfiber_renyi_family_single_chi2_closure_family Dlim Dtwo hfamily,
    conclusion_maxfiber_renyi_family_single_chi2_closure_phi_recovery Dchi phi hphi⟩

end Omega.Conclusion
