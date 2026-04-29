import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-continuous-strict-drop-implies-discrete-finite-certificate`. -/
theorem paper_conclusion_continuous_strict_drop_implies_discrete_finite_certificate
    (K : ℝ) (Ktilde : ℕ → ℝ) (eps : ℝ) (heps : 0 < eps) (hdrop : K ≤ 1 - eps)
    (hconv : ∃ M0, ∀ M ≥ M0, |Ktilde M - K| ≤ eps / 2) :
    ∃ M0, ∀ M ≥ M0, Ktilde M ≤ 1 - eps / 2 := by
  rcases hconv with ⟨M0, hM0⟩
  refine ⟨M0, ?_⟩
  intro M hM
  have hupper : Ktilde M - K ≤ eps / 2 := (abs_le.mp (hM0 M hM)).2
  have hpos : 0 < eps := heps
  linarith [hpos]

end Omega.Conclusion
