import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-bernoulli-zeta-tower-explicit-triangular-inversion`. -/
theorem paper_conclusion_bernoulli_zeta_tower_explicit_triangular_inversion
    (coefficientRecovered bernoulliRecovered zetaRecovered : Nat → Prop)
    (hstep : ∀ r, 1 ≤ r →
      (∀ s, 1 ≤ s → s < r → coefficientRecovered s) → coefficientRecovered r)
    (hBernoulli : ∀ r, coefficientRecovered r → bernoulliRecovered r)
    (hZeta : ∀ r, bernoulliRecovered r → zetaRecovered r) :
    ∀ r, 1 ≤ r →
      coefficientRecovered r ∧ bernoulliRecovered r ∧ zetaRecovered r := by
  have hcoeff : ∀ r, 1 ≤ r → coefficientRecovered r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hr
        exact hstep r hr (fun s hs hsr => ih s hsr hs)
  intro r hr
  have hc : coefficientRecovered r := hcoeff r hr
  have hb : bernoulliRecovered r := hBernoulli r hc
  exact ⟨hc, hb, hZeta r hb⟩

end Omega.Conclusion
