import Mathlib.Tactic
import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Closed form for one path component of length `ell`: its quotient fiber has Fibonacci size. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberComponent
    (ell : ℕ) : ℕ :=
  Nat.fib (ell + 2)

/-- Closed form for the residual alphabet ceiling contributed by one component. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingComponent
    (ell : ℕ) : ℕ :=
  (ell + 1) / 2

/-- The one-component product model used to witness the separation. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberProduct
    (ell : ℕ) : ℕ :=
  conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberComponent ell

/-- The corresponding linear ceiling-sum model. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingSum
    (ell : ℕ) : ℕ :=
  conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingComponent ell

/-- Quotient incompleteness occurs once the Fibonacci fiber strictly exceeds the available
ceiling-sum alphabet. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_quotientIncomplete
    (ell : ℕ) : Prop :=
  conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingSum ell <
    conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberProduct ell

/-- The residual obstruction: a statistically sufficient scalar still misses quotient structure
whenever the quotient-incompleteness inequality holds. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_residualObstruction
    (ell : ℕ) : Prop :=
  conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_quotientIncomplete ell →
    ∃ residualBlocks : ℕ,
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingSum ell <
        residualBlocks ∧
      residualBlocks =
        conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberProduct ell

lemma conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceiling_lt_fib
    {ell : ℕ} (hell : 1 ≤ ell) :
    conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingSum ell <
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberProduct ell := by
  have hceil :
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingSum ell ≤
        ell := by
    unfold conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingSum
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingComponent
    omega
  have hfib : ell + 1 ≤ Nat.fib (ell + 2) := fib_succ_succ_ge_succ ell
  unfold conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberProduct
    conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberComponent
  omega

lemma conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_obstruction
    (ell : ℕ) :
    conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_residualObstruction
      ell := by
  intro hincomplete
  exact
    ⟨conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberProduct ell,
      hincomplete, rfl⟩

/-- Concrete paper-facing statement for the statistical-versus-quotient sufficiency split. -/
def conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_statement : Prop :=
  (∀ ell : ℕ,
    conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_fiberComponent ell =
      Nat.fib (ell + 2)) ∧
    (∀ ell : ℕ,
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceilingComponent ell =
        (ell + 1) / 2) ∧
    (∀ ell : ℕ, 1 ≤ ell →
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_quotientIncomplete
        ell) ∧
    (∀ ell : ℕ,
      conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_residualObstruction
        ell)

/-- Paper label:
`cor:conclusion-statistical-sufficiency-vs-quotient-sufficiency-separation`. -/
theorem paper_conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation :
    conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ell
    rfl
  · intro ell
    rfl
  · intro ell hell
    exact conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_ceiling_lt_fib hell
  · intro ell
    exact conclusion_statistical_sufficiency_vs_quotient_sufficiency_separation_obstruction ell

end Omega.Conclusion
