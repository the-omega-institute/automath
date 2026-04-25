import Mathlib.Tactic

namespace Omega.Conclusion

universe u v

/-- Concrete finite-rank exact-ledger data: an injective multiplicative ledger into an additive
target with a chosen finite-rank bound. -/
structure conclusion_finite_rank_exact_ledger_completion_fiber_empty_data where
  source : Type u
  target : Type v
  sourceCommMonoid : CommMonoid source
  targetAddCommGroup : AddCommGroup target
  targetModule : Module ℤ target
  rankBound : ℕ
  ledger : source → target
  ledger_injective : Function.Injective ledger

/-- A forbidden exact-completion fiber point is a nontrivial pair collapsed by the ledger. -/
def conclusion_finite_rank_exact_ledger_completion_fiber_empty_fiber
    (D : conclusion_finite_rank_exact_ledger_completion_fiber_empty_data) : Type (max u v) :=
  {p : D.source × D.source // p.1 ≠ p.2 ∧ D.ledger p.1 = D.ledger p.2}

/-- The exact-completion fiber over an injective ledger is empty. -/
def conclusion_finite_rank_exact_ledger_completion_fiber_empty_statement
    (D : conclusion_finite_rank_exact_ledger_completion_fiber_empty_data) : Prop :=
  IsEmpty (conclusion_finite_rank_exact_ledger_completion_fiber_empty_fiber D)

/-- Paper label: `thm:conclusion-finite-rank-exact-ledger-completion-fiber-empty`. -/
theorem paper_conclusion_finite_rank_exact_ledger_completion_fiber_empty
    (D : conclusion_finite_rank_exact_ledger_completion_fiber_empty_data) :
    conclusion_finite_rank_exact_ledger_completion_fiber_empty_statement D := by
  refine ⟨?_⟩
  rintro ⟨⟨x, y⟩, hxy_ne, hxy_eq⟩
  exact hxy_ne (D.ledger_injective hxy_eq)

end Omega.Conclusion
