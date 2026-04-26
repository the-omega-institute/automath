import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-cyclic-escort-full-axis-ordering`. -/
theorem paper_conclusion_window6_cyclic_escort_full_axis_ordering
    (lambda1 lambda2 lambda3 : ℝ → ℝ) (qax : ℝ)
    (hneg : ∀ q, q < 0 → lambda3 q > lambda2 q ∧ lambda2 q > lambda1 q)
    (hsmall : ∀ q, 0 < q → q < qax → lambda1 q > lambda2 q ∧ lambda2 q > lambda3 q)
    (hlarge : ∀ q, qax < q → lambda2 q > lambda1 q ∧ lambda1 q > lambda3 q)
    (hiso : lambda1 0 = lambda2 0 ∧ lambda2 0 = lambda3 0)
    (hcross : lambda1 qax = lambda2 qax) :
    (∀ q, q < 0 → lambda3 q > lambda2 q ∧ lambda2 q > lambda1 q) ∧
      (∀ q, 0 < q → q < qax → lambda1 q > lambda2 q ∧ lambda2 q > lambda3 q) ∧
        (∀ q, qax < q → lambda2 q > lambda1 q ∧ lambda1 q > lambda3 q) ∧
          lambda1 0 = lambda2 0 ∧ lambda2 0 = lambda3 0 ∧
            lambda1 qax = lambda2 qax := by
  exact ⟨hneg, hsmall, hlarge, hiso.1, hiso.2, hcross⟩

end Omega.Conclusion
