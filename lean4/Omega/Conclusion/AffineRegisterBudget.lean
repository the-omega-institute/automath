import Mathlib.Tactic

namespace Omega.Conclusion

/-- Any injective encoding of `p^r` affine fibers into `R` registers forces `R ≥ p^r`.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem registerBudget_lower_bound (p r R : Nat)
    (hinj : ∃ f : Fin (p ^ r) → Fin R, Function.Injective f) :
    p ^ r ≤ R := by
  rcases hinj with ⟨f, hf⟩
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The lower bound is sharp by the identity encoding.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem registerBudget_sharp (p r : Nat) :
    ∃ f : Fin (p ^ r) → Fin (p ^ r), Function.Injective f := by
  exact ⟨id, fun _ _ h => h⟩

/-- Minimal register budget corollary.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem registerBudget_min_card (p r R : Nat)
    (h : ∃ f : Fin (p ^ r) → Fin R, Function.Injective f) :
    p ^ r ≤ R :=
  registerBudget_lower_bound p r R h

end Omega.Conclusion
