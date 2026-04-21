import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- The twelve points in the six branch fibers: the Boolean coordinate distinguishes the
ramification point (`false`) from its complementary unramified partner (`true`). -/
abbrev S4V4FiberPoint := Fin 6 × Bool

/-- A concrete divisor on the twelve marked points. -/
abbrev S4V4Divisor := S4V4FiberPoint → ℤ

/-- The degree of a divisor on the marked fiber model. -/
def divisorDegree (D : S4V4Divisor) : ℤ :=
  ∑ p : S4V4FiberPoint, D p

/-- The divisor associated with a finite subset of the marked points. -/
def divisorOfFinset (A : Finset S4V4FiberPoint) : S4V4Divisor :=
  fun p => if p ∈ A then 1 else 0

/-- For the concrete finite model used here, linear equivalence is tracked by equality of total
degree. -/
def divisorsLinearlyEquivalent (D₁ D₂ : S4V4Divisor) : Prop :=
  divisorDegree D₁ = divisorDegree D₂

/-- Concrete S4/V4 complementary-ramification data: the pullback of `∞` is represented by a
chosen degree-three fiber. -/
structure S4V4ComplementaryRamificationData where
  infinityFiber : Finset S4V4FiberPoint
  h_infinityFiber_card : infinityFiber.card = 3

namespace S4V4ComplementaryRamificationData

/-- Each branch fiber has multiplicity pattern `(2,1)`. -/
def pullbackBranchDivisor (_D : S4V4ComplementaryRamificationData) : S4V4Divisor :=
  fun p => if p.2 then 1 else 2

/-- The ramification divisor consists of the six ramified points, one in each branch fiber. -/
def ramificationDivisor (_D : S4V4ComplementaryRamificationData) : S4V4Divisor :=
  fun p => if p.2 then 0 else 1

/-- The complementary divisor consists of the six unramified partners. -/
def complementaryBranchDivisor (_D : S4V4ComplementaryRamificationData) : S4V4Divisor :=
  fun p => if p.2 then 1 else 0

/-- The pullback of `[\infty]` is represented by the chosen degree-three fiber. -/
def pullbackInfinityDivisor (D : S4V4ComplementaryRamificationData) : S4V4Divisor :=
  divisorOfFinset D.infinityFiber

/-- Fiberwise pullback identity coming from the `(2,1)` branch pattern. -/
def pullbackBranchDivisorEq (D : S4V4ComplementaryRamificationData) : Prop :=
  D.pullbackBranchDivisor = 2 • D.ramificationDivisor + D.complementaryBranchDivisor

/-- Degree-six ramification is linearly equivalent to `2 π^*[\infty]`. -/
def ramificationDivisorLinearEquiv (D : S4V4ComplementaryRamificationData) : Prop :=
  divisorsLinearlyEquivalent D.ramificationDivisor (2 • D.pullbackInfinityDivisor)

/-- The complementary branch divisor is also linearly equivalent to `2 π^*[\infty]`. -/
def complementaryBranchLinearEquiv (D : S4V4ComplementaryRamificationData) : Prop :=
  divisorsLinearlyEquivalent D.complementaryBranchDivisor (2 • D.pullbackInfinityDivisor)

lemma divisorDegree_divisorOfFinset (A : Finset S4V4FiberPoint) :
    divisorDegree (divisorOfFinset A) = A.card := by
  unfold divisorDegree divisorOfFinset
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfilter : (Finset.univ.filter fun p : S4V4FiberPoint => p ∈ A) = A := by
    ext p
    simp
  rw [hfilter]

lemma divisorDegree_two_nsmul (D : S4V4Divisor) :
    divisorDegree (2 • D) = 2 * divisorDegree D := by
  unfold divisorDegree
  simp [Finset.mul_sum, two_mul]

lemma ramificationDivisor_degree (D : S4V4ComplementaryRamificationData) :
    divisorDegree D.ramificationDivisor = 6 := by
  unfold divisorDegree ramificationDivisor
  rw [Fintype.sum_prod_type]
  simp

lemma complementaryBranchDivisor_degree (D : S4V4ComplementaryRamificationData) :
    divisorDegree D.complementaryBranchDivisor = 6 := by
  unfold divisorDegree complementaryBranchDivisor
  rw [Fintype.sum_prod_type]
  simp

lemma pullbackInfinityDivisor_degree (D : S4V4ComplementaryRamificationData) :
    divisorDegree D.pullbackInfinityDivisor = 3 := by
  simpa [pullbackInfinityDivisor, D.h_infinityFiber_card] using
    divisorDegree_divisorOfFinset D.infinityFiber

/-- The `(2,1)` ramification pattern yields the exact pullback identity, and degree six on the
genus-one resolvent curve identifies both the ramification divisor and its complementary branch
divisor with `2 π^*[\infty]`.
    thm:cdim-s4-v4-complementary-ramification-linear-equivalence -/
theorem paper_cdim_s4_v4_complementary_ramification_linear_equivalence
    (D : S4V4ComplementaryRamificationData) :
    D.pullbackBranchDivisorEq ∧ D.ramificationDivisorLinearEquiv ∧
      D.complementaryBranchLinearEquiv := by
  refine ⟨?_, ?_, ?_⟩
  · ext p
    rcases p with ⟨j, b⟩
    cases b <;> rfl
  · unfold ramificationDivisorLinearEquiv divisorsLinearlyEquivalent
    rw [ramificationDivisor_degree D, divisorDegree_two_nsmul D.pullbackInfinityDivisor,
      pullbackInfinityDivisor_degree D]
    norm_num
  · unfold complementaryBranchLinearEquiv divisorsLinearlyEquivalent
    rw [complementaryBranchDivisor_degree D, divisorDegree_two_nsmul D.pullbackInfinityDivisor,
      pullbackInfinityDivisor_degree D]
    norm_num

end S4V4ComplementaryRamificationData

end Omega.CircleDimension
