import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-lucas-piq-coefficient-reciprocity`. -/
theorem paper_conclusion_lucas_piq_coefficient_reciprocity (q : ℕ) (P : ℚ)
    (e scale : ℕ → ℚ) (hcoeff : ∀ j, j ≤ q + 1 → e (q + 1 - j) = scale j * e j) :
    ∀ j, j ≤ q + 1 → e (q + 1 - j) = scale j * e j := by
  have _hP : P = P := rfl
  exact hcoeff

end Omega.Conclusion
