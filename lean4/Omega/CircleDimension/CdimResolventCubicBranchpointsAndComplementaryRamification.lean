import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.CdimS4V4KummerModelAndResolventRecovery

namespace Omega.CircleDimension

/-- Concrete wrapper for the audited resolvent-cubic branchpoint statement. -/
structure cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data where
  cdim_resolvent_cubic_branchpoints_and_complementary_ramification_witness : Unit := ()

/-- The six branch values are indexed by `Fin 6`. -/
def cdim_resolvent_cubic_branchpoints_and_complementary_ramification_branch_values :
    Finset (Fin 6) :=
  Finset.univ

/-- The six ramified points, one in each branch fiber. -/
def cdim_resolvent_cubic_branchpoints_and_complementary_ramification_ramification_points :
    Finset S4V4FiberPoint :=
  Finset.univ.filter fun p => p.2 = false

/-- The six complementary unramified points, one in each branch fiber. -/
def cdim_resolvent_cubic_branchpoints_and_complementary_ramification_complementary_points :
    Finset S4V4FiberPoint :=
  Finset.univ.filter fun p => p.2 = true

/-- A concrete degree-three model for `π^*[\infty]`. -/
def cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber :
    Finset S4V4FiberPoint :=
  Finset.univ.filter fun p => p.2 = true ∧ p.1.val < 3

lemma cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber_card :
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber.card = 3 := by
  decide

lemma cdim_resolvent_cubic_branchpoints_and_complementary_ramification_factor_at_zero (z : ℂ) :
    cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial 0 z =
      (z + 1) ^ 2 * (z - 1) := by
  unfold cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial
  ring

lemma cdim_resolvent_cubic_branchpoints_and_complementary_ramification_factor_at_one (z : ℂ) :
    cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial 1 z =
      (z + 3) ^ 2 * (z - 3) := by
  unfold cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial
  ring

namespace cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data

/-- Concrete paper-facing formulation: six branch fibers, explicit `y = 0, 1` factorizations,
and the complementary branch divisor from the existing S4/V4 bookkeeping package. -/
def statement (_D : cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data) :
    Prop :=
  let R : S4V4ComplementaryRamificationData := ⟨
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber,
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber_card
  ⟩
  cdim_resolvent_cubic_branchpoints_and_complementary_ramification_branch_values.card = 6 ∧
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_ramification_points.card = 6 ∧
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_complementary_points.card = 6 ∧
    (∀ i : Fin 6,
      (i, false) ∈
          cdim_resolvent_cubic_branchpoints_and_complementary_ramification_ramification_points ∧
        (i, true) ∈
          cdim_resolvent_cubic_branchpoints_and_complementary_ramification_complementary_points) ∧
    (∀ z : ℂ,
      cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial 0 z =
        (z + 1) ^ 2 * (z - 1)) ∧
    (∀ z : ℂ,
      cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial 1 z =
        (z + 3) ^ 2 * (z - 3)) ∧
    divisorDegree R.complementaryBranchDivisor = 6 ∧
    R.complementaryBranchLinearEquiv

end cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data

open cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data

/-- Paper label: `prop:cdim-resolvent-cubic-branchpoints-and-complementary-ramification`. -/
theorem paper_cdim_resolvent_cubic_branchpoints_and_complementary_ramification
    (D : cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data) : D.statement := by
  let R : S4V4ComplementaryRamificationData := ⟨
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber,
    cdim_resolvent_cubic_branchpoints_and_complementary_ramification_infinity_fiber_card
  ⟩
  have hramification :
      R.complementaryBranchLinearEquiv := by
    exact
      (S4V4ComplementaryRamificationData.paper_cdim_s4_v4_complementary_ramification_linear_equivalence
        R).2.2
  dsimp [cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data.statement, R]
  refine ⟨by simp [cdim_resolvent_cubic_branchpoints_and_complementary_ramification_branch_values],
    by decide, by decide, ?_, ?_, ?_, ?_, hramification⟩
  · intro i
    simp [cdim_resolvent_cubic_branchpoints_and_complementary_ramification_ramification_points,
      cdim_resolvent_cubic_branchpoints_and_complementary_ramification_complementary_points]
  · intro z
    exact cdim_resolvent_cubic_branchpoints_and_complementary_ramification_factor_at_zero z
  · intro z
    exact cdim_resolvent_cubic_branchpoints_and_complementary_ramification_factor_at_one z
  · exact S4V4ComplementaryRamificationData.complementaryBranchDivisor_degree R

end Omega.CircleDimension
