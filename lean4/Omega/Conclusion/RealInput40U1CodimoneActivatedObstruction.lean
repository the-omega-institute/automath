import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-u1-codimone-activated-obstruction`. -/
theorem paper_conclusion_realinput40_u1_codimone_activated_obstruction (G Gtilde : ℝ → ℝ → ℝ)
    (lambdaAct : ℝ → ℝ) (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η)
    (hfactor : ∀ lam u, |lam| < η → |u - 1| < δ →
      G lam u = (lam - lambdaAct u) * Gtilde lam u)
    (hnonzero : ∀ lam u, |lam| < η → |u - 1| < δ → Gtilde lam u ≠ 0) :
    ∀ lam u, |lam| < η → |u - 1| < δ → G lam u = 0 → lam = lambdaAct u := by
  have _ := hδ
  have _ := hη
  intro lam u hlam hu hG
  have hprod : (lam - lambdaAct u) * Gtilde lam u = 0 := by
    rw [← hfactor lam u hlam hu, hG]
  have hleft : lam - lambdaAct u = 0 := by
    exact Or.resolve_right (mul_eq_zero.mp hprod) (hnonzero lam u hlam hu)
  linarith

end Omega.Conclusion
