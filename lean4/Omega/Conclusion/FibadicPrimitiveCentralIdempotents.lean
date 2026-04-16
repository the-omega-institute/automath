import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Fibadic primitive central idempotents

This file records the rational 0/1 classification of idempotent coordinates and packages it as a
finite-support theorem.
-/

namespace Omega.Conclusion.FibadicPrimitiveCentralIdempotents

/-- A rational idempotent is necessarily `0` or `1`.
    thm:conclusion-fibadic-finite-layer-gcd-primitive-central-idempotents -/
lemma rat_eq_zero_or_one_of_mul_self_eq (x : ℚ) (hx : x * x = x) : x = 0 ∨ x = 1 := by
  have h : x * (x - 1) = 0 := by
    nlinarith [hx]
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Paper seed: a rational-valued finite family of idempotents is the indicator function of a
subset.
    thm:conclusion-fibadic-finite-layer-gcd-primitive-central-idempotents -/
theorem paper_conclusion_fibadic_primitive_central_idempotents_seeds
    {ι : Type} [DecidableEq ι] [Fintype ι] (e : ι → ℚ)
    (he : ∀ i, e i * e i = e i) :
    ∃ S : Finset ι, ∀ i, e i = if i ∈ S then 1 else 0 := by
  let S : Finset ι := Finset.univ.filter fun i => e i = 1
  refine ⟨S, ?_⟩
  intro i
  have hi01 := rat_eq_zero_or_one_of_mul_self_eq (e i) (he i)
  by_cases hi : i ∈ S
  · have hei1 : e i = 1 := (Finset.mem_filter.mp hi).2
    simp [S, hi, hei1]
  · rcases hi01 with h0 | h1
    · simp [S, hi, h0]
    · exfalso
      exact hi (by simp [S, h1])

/-- Paper-facing package clone for the finite idempotent classification.
    thm:conclusion-fibadic-finite-layer-gcd-primitive-central-idempotents -/
theorem paper_conclusion_fibadic_primitive_central_idempotents_package
    {ι : Type} [DecidableEq ι] [Fintype ι] (e : ι → ℚ)
    (he : ∀ i, e i * e i = e i) :
    ∃ S : Finset ι, ∀ i, e i = if i ∈ S then 1 else 0 :=
  paper_conclusion_fibadic_primitive_central_idempotents_seeds e he

end Omega.Conclusion.FibadicPrimitiveCentralIdempotents
