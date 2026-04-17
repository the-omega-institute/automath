import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Uniform Reynolds average over a finite fiber. -/
noncomputable def reynoldsAverage {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ a ∈ s, f a) / s.card

/-- In this finite uniform model, the conditional expectation is the same fiber average. -/
noncomputable def conditionalExpectation {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  reynoldsAverage s f

/-- The original quadratic risk on a finite fiber. -/
noncomputable def originalRisk {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ a ∈ s, (f a) ^ 2) / s.card

/-- The Reynolds-symmetrized quadratic risk. -/
noncomputable def reynoldsRisk {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (reynoldsAverage s f) ^ 2

/-- The Jensen inequality package for the quadratic risk. -/
def reynoldsRiskLeOriginal {α : Type*} (s : Finset α) (f : α → ℝ) : Prop :=
  reynoldsRisk s f ≤ originalRisk s f

/-- The strict-convexity branch is triggered exactly when equality occurs. -/
def strictConvexCase {α : Type*} (s : Finset α) (f : α → ℝ) : Prop :=
  reynoldsRisk s f = originalRisk s f

/-- Equality in the quadratic Jensen inequality is equivalent to fiberwise constancy. -/
def equalityIffFiberwiseConstant {α : Type*} (s : Finset α) (f : α → ℝ) : Prop :=
  reynoldsRisk s f = originalRisk s f ↔ ∀ a ∈ s, f a = reynoldsAverage s f

/-- Reynolds averaging is the conditional expectation onto the invariant subalgebra. -/
def reynoldsEqualsConditionalExpectation {α : Type*} (s : Finset α) (f : α → ℝ) : Prop :=
  reynoldsAverage s f = conditionalExpectation s f

lemma reynoldsRiskLeOriginal_proof {α : Type*} (s : Finset α) (f : α → ℝ) :
    reynoldsRiskLeOriginal s f := by
  unfold reynoldsRiskLeOriginal reynoldsRisk originalRisk reynoldsAverage
  simpa [pow_two] using
    (sum_div_card_sq_le_sum_sq_div_card (s := s) (f := fun a => f a))

lemma equalityIffFiberwiseConstant_proof {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    equalityIffFiberwiseConstant s f := by
  classical
  refine ⟨?_, ?_⟩
  · intro hEq a ha
    have hMain :
        ∑ x ∈ s, (f x - reynoldsAverage s f) ^ 2 = 0 := by
      let μ := reynoldsAverage s f
      have hs0 : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast hs.card_ne_zero
      have hsum :
          ∑ x ∈ s, (f x - μ) ^ 2 =
            (∑ x ∈ s, (f x) ^ 2) - ((∑ x ∈ s, f x) ^ 2) / s.card := by
        calc
          ∑ x ∈ s, (f x - μ) ^ 2
              = ∑ x ∈ s, ((f x) ^ 2 - (2 * μ) * f x + μ ^ 2) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  ring
          _ = (∑ x ∈ s, (f x) ^ 2) - ∑ x ∈ s, (2 * μ) * f x + ∑ x ∈ s, μ ^ 2 := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          _ = (∑ x ∈ s, (f x) ^ 2) - (2 * μ) * (∑ x ∈ s, f x) + s.card * μ ^ 2 := by
                rw [Finset.mul_sum]
                simp
          _ = (∑ x ∈ s, (f x) ^ 2) - ((∑ x ∈ s, f x) ^ 2) / s.card := by
                unfold μ reynoldsAverage
                field_simp [hs0]
                ring
      have hEq' :
          ((∑ x ∈ s, f x) ^ 2) / s.card = ∑ x ∈ s, (f x) ^ 2 := by
        have hEqRisk :
            ((∑ x ∈ s, f x) / s.card) ^ 2 = (∑ x ∈ s, (f x) ^ 2) / s.card := by
          simpa [reynoldsRisk, originalRisk, reynoldsAverage] using hEq
        have hcard_pos : 0 < (s.card : ℝ) := by
          exact_mod_cast hs.card_pos
        field_simp [hcard_pos.ne'] at hEqRisk ⊢
        linarith
      have hEq'' :
          (∑ x ∈ s, (f x) ^ 2) - ((∑ x ∈ s, f x) ^ 2) / s.card = 0 := by
        linarith
      simpa [μ, hEq''] using hsum
    have hNonneg : ∀ x ∈ s, 0 ≤ (f x - reynoldsAverage s f) ^ 2 := by
      intro x hx
      positivity
    have hZero :
        (f a - reynoldsAverage s f) ^ 2 = 0 := by
      apply Finset.sum_eq_zero_iff_of_nonneg hNonneg |>.mp hMain a ha
    nlinarith [sq_nonneg (f a - reynoldsAverage s f)]
  · intro hConst
    have hs0 : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast hs.card_ne_zero
    have hsum :
        ∑ x ∈ s, f x = s.card * reynoldsAverage s f := by
      calc
        ∑ x ∈ s, f x = ∑ x ∈ s, reynoldsAverage s f := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact hConst x hx
        _ = s.card * reynoldsAverage s f := by simp
    have hsquares :
        ∑ x ∈ s, (f x) ^ 2 = s.card * (reynoldsAverage s f) ^ 2 := by
      calc
        ∑ x ∈ s, (f x) ^ 2 = ∑ x ∈ s, (reynoldsAverage s f) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [hConst x hx]
        _ = s.card * (reynoldsAverage s f) ^ 2 := by simp
    unfold reynoldsRisk originalRisk reynoldsAverage
    field_simp [hs0]
    rw [hsum, hsquares]
    ring

/-- Paper-facing finite Reynolds package for quadratic risk: Jensen gives monotonicity, equality
forces fiberwise constancy, and the Reynolds average is the conditional expectation onto the
invariant algebra.
    prop:op-algebra-fold-reynolds-risk-convex -/
theorem paper_op_algebra_fold_reynolds_risk_convex {α : Type*}
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    reynoldsRiskLeOriginal s f ∧
      (strictConvexCase s f → equalityIffFiberwiseConstant s f) ∧
      reynoldsEqualsConditionalExpectation s f := by
  refine ⟨reynoldsRiskLeOriginal_proof s f, ?_, rfl⟩
  intro _
  exact equalityIffFiberwiseConstant_proof s hs f

end Omega.OperatorAlgebra
