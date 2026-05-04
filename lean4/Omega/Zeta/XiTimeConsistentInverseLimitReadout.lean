import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-consistent-inverse-limit-readout`. -/
theorem paper_xi_time_consistent_inverse_limit_readout {X : ℕ → Type}
    (p : ∀ {i j : ℕ}, i ≤ j → X j → X i) (x : ∀ m, X m)
    (hcompat : ∀ {i j : ℕ} (hij : i ≤ j), p (i := i) (j := j) hij (x j) = x i) :
    ∃! y : { y : ∀ m, X m //
      ∀ {i j : ℕ} (hij : i ≤ j), p (i := i) (j := j) hij (y j) = y i },
      ∀ m, y.1 m = x m := by
  refine ⟨⟨x, ?_⟩, ?_, ?_⟩
  · intro i j hij
    exact hcompat hij
  · intro m
    rfl
  · intro y hy
    apply Subtype.ext
    funext m
    exact hy m

end Omega.Zeta
