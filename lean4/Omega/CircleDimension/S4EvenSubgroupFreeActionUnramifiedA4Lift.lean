import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete arithmetic package for the `S₄/A₄/V₄` quotient tower used in the genus computation. -/
structure killo_s4_even_subgroup_free_action_unramified_a4_lift_data where
  a4FixedPointCount : ℕ
  xToHRamificationCount : ℕ
  hToP1Degree : ℕ
  hToP1BranchPointCount : ℕ
  a4OverV4QuotientOrder : ℕ
  c6ToHDegree : ℕ
  c6ToHRamificationCount : ℕ
  a4FixedPointCount_eq : a4FixedPointCount = 0
  xToHRamificationCount_eq : xToHRamificationCount = 0
  hToP1Degree_eq : hToP1Degree = 2
  hToP1BranchPointCount_eq : hToP1BranchPointCount = 12
  a4OverV4QuotientOrder_eq : a4OverV4QuotientOrder = 3
  c6ToHDegree_eq : c6ToHDegree = a4OverV4QuotientOrder
  c6ToHRamificationCount_eq : c6ToHRamificationCount = 0

namespace killo_s4_even_subgroup_free_action_unramified_a4_lift_data

/-- Freeness of the `A₄`-action is encoded by vanishing fixed-point count. -/
def a4ActsFreely (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : Prop :=
  D.a4FixedPointCount = 0

/-- The quotient map `X → H` is unramified when the ramification count vanishes. -/
def xToHUnramified (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : Prop :=
  D.xToHRamificationCount = 0

/-- Riemann--Hurwitz for a double cover of `ℙ¹` branched above twelve points gives genus `5`. -/
def genusH (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : ℕ :=
  D.hToP1BranchPointCount / 2 - 1

/-- The intermediate quotient `H → ℙ¹` has degree `2`. -/
def hToP1IsDoubleCover (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : Prop :=
  D.hToP1Degree = 2

/-- The quotient `A₄/V₄ ≅ C₃` forces `C₆ → H` to be a cyclic triple cover. -/
def c6ToHIsCyclicTripleCover
    (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : Prop :=
  D.c6ToHDegree = 3

/-- The `C₆ → H` cover is unramified when its ramification count vanishes. -/
def c6ToHUnramified (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : Prop :=
  D.c6ToHRamificationCount = 0

/-- Riemann--Hurwitz for an unramified cyclic triple cover of a genus-`5` curve gives genus `13`.
-/
def genusC6 (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) : ℕ :=
  D.c6ToHDegree * (D.genusH - 1) + 1

end killo_s4_even_subgroup_free_action_unramified_a4_lift_data

open killo_s4_even_subgroup_free_action_unramified_a4_lift_data

/-- Paper label: `thm:killo-s4-even-subgroup-free-action-unramified-a4-lift`. -/
theorem paper_killo_s4_even_subgroup_free_action_unramified_a4_lift
    (D : killo_s4_even_subgroup_free_action_unramified_a4_lift_data) :
    D.a4ActsFreely ∧ D.xToHUnramified ∧ D.genusH = 5 ∧ D.hToP1IsDoubleCover ∧
      D.c6ToHIsCyclicTripleCover ∧ D.c6ToHUnramified ∧ D.genusC6 = 13 := by
  have hgenusH : D.genusH = 5 := by
    simp [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.genusH,
      D.hToP1BranchPointCount_eq]
  have hc6degree : D.c6ToHDegree = 3 := by
    rw [D.c6ToHDegree_eq, D.a4OverV4QuotientOrder_eq]
  have hgenusC6 : D.genusC6 = 13 := by
    simp [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.genusC6, hc6degree, hgenusH]
  refine ⟨?_, ?_, hgenusH, ?_, ?_, ?_, hgenusC6⟩
  · simpa [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.a4ActsFreely] using
      D.a4FixedPointCount_eq
  · simpa [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.xToHUnramified] using
      D.xToHRamificationCount_eq
  · simpa [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.hToP1IsDoubleCover] using
      D.hToP1Degree_eq
  · simpa
      [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.c6ToHIsCyclicTripleCover] using
      hc6degree
  · simpa [killo_s4_even_subgroup_free_action_unramified_a4_lift_data.c6ToHUnramified] using
      D.c6ToHRamificationCount_eq

end Omega.CircleDimension
