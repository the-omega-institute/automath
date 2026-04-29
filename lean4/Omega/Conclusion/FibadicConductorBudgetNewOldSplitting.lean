import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-fibadic-conductor-budget-new-old-splitting`. -/
theorem paper_conclusion_fibadic_conductor_budget_new_old_splitting
    (F Pi Q z : ℕ → ℕ) (vp : ℕ → ℕ → ℕ)
    (hQ : ∀ d, 3 ≤ d → F d = Pi d * Q d)
    (hprimitive : ∀ d, 3 ≤ d →
      Q d =
        ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e ∧ e < d), Pi e)
    (hvaluation : ∀ p d, 3 ≤ d →
      vp p (Q d) =
        ((Finset.range (d + 1)).filter
          (fun k => 1 ≤ k ∧ z (p ^ k) ∣ d ∧ z (p ^ k) < d)).card) :
    ∀ d, 3 ≤ d →
      Q d =
          ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e ∧ e < d), Pi e ∧
        F d =
          Pi d *
            ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e ∧ e < d), Pi e ∧
        ∀ p,
          vp p (Q d) =
            ((Finset.range (d + 1)).filter
              (fun k => 1 ≤ k ∧ z (p ^ k) ∣ d ∧ z (p ^ k) < d)).card := by
  intro d hd
  have hQd := hprimitive d hd
  refine ⟨hQd, ?_, fun p => hvaluation p d hd⟩
  rw [hQ d hd, hQd]

end Omega.Conclusion
