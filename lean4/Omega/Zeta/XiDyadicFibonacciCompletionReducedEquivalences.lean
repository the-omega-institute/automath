import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-dyadic-fibonacci-completion-reduced-equivalences`. -/
theorem paper_xi_dyadic_fibonacci_completion_reduced_equivalences {ι : Type*}
    (e : ι → ℕ) (reduced jacobson_zero product_fields : Prop)
    (hred : reduced ↔ ∀ p, e p = 1) (hjac : jacobson_zero ↔ ∀ p, e p = 1)
    (hprod : product_fields ↔ ∀ p, e p = 1) :
    (∀ p, e p = 1) ↔ reduced ∧ jacobson_zero ∧ product_fields := by
  constructor
  · intro hone
    exact ⟨hred.2 hone, hjac.2 hone, hprod.2 hone⟩
  · intro h
    exact hred.1 h.1

end Omega.Zeta
