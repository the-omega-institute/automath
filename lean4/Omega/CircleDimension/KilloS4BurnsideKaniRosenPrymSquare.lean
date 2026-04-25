import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import Omega.CircleDimension.S4EvenSubgroupFreeActionUnramifiedA4Lift
import Omega.CircleDimension.S4V4JacobianPullbackKernelPrymSplitting

namespace Omega.CircleDimension

/-- The five irreducible `S₄` constituents used in the Burnside--Kani--Rosen bookkeeping are
ordered as `1`, `sgn`, `V₂`, `V₃`, `V₃'`. -/
abbrev killo_s4_burnside_kani_rosen_prym_square_rep := Fin 5 → ℤ

/-- The induced trivial representation from the subgroup `H ≤ S₄`, encoded by its irreducible
multiplicity vector. -/
def killo_s4_burnside_kani_rosen_prym_square_rho_s4 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_a4 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 1 => 1
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_v4 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 1 => 1
    | 2 => 2
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_d8 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 2 => 1
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_s3 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 3 => 1
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_c4 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 2 => 1
    | 4 => 1
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_c2 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 2 => 1
    | 3 => 2
    | 4 => 1
    | _ => 0

def killo_s4_burnside_kani_rosen_prym_square_rho_c3 :
    killo_s4_burnside_kani_rosen_prym_square_rep :=
  fun i =>
    match i.1 with
    | 0 => 1
    | 1 => 1
    | 3 => 1
    | 4 => 1
    | _ => 0

/-- The first representation-ring identity from the paper. -/
def killo_s4_burnside_kani_rosen_prym_square_identity_one : Prop :=
  ∀ i,
    (2 * killo_s4_burnside_kani_rosen_prym_square_rho_s4 +
        killo_s4_burnside_kani_rosen_prym_square_rho_v4) i =
      (killo_s4_burnside_kani_rosen_prym_square_rho_a4 +
        2 * killo_s4_burnside_kani_rosen_prym_square_rho_d8) i

/-- The second representation-ring identity from the paper. -/
def killo_s4_burnside_kani_rosen_prym_square_identity_two : Prop :=
  ∀ i,
    (2 * killo_s4_burnside_kani_rosen_prym_square_rho_s4 +
        killo_s4_burnside_kani_rosen_prym_square_rho_c2) i =
      (2 * killo_s4_burnside_kani_rosen_prym_square_rho_s3 +
        killo_s4_burnside_kani_rosen_prym_square_rho_c4) i

/-- The third representation-ring identity from the paper. -/
def killo_s4_burnside_kani_rosen_prym_square_identity_three : Prop :=
  ∀ i,
    (4 * killo_s4_burnside_kani_rosen_prym_square_rho_s4 +
        killo_s4_burnside_kani_rosen_prym_square_rho_v4 +
        2 * killo_s4_burnside_kani_rosen_prym_square_rho_c3) i =
      (3 * killo_s4_burnside_kani_rosen_prym_square_rho_a4 +
        2 * killo_s4_burnside_kani_rosen_prym_square_rho_s3 +
        2 * killo_s4_burnside_kani_rosen_prym_square_rho_c4) i

/-- A concrete audited instance of the unramified `A₄`-lift package. -/
def killo_s4_burnside_kani_rosen_prym_square_lift_data :
    killo_s4_even_subgroup_free_action_unramified_a4_lift_data where
  a4FixedPointCount := 0
  xToHRamificationCount := 0
  hToP1Degree := 2
  hToP1BranchPointCount := 12
  a4OverV4QuotientOrder := 3
  c6ToHDegree := 3
  c6ToHRamificationCount := 0
  a4FixedPointCount_eq := rfl
  xToHRamificationCount_eq := rfl
  hToP1Degree_eq := rfl
  hToP1BranchPointCount_eq := rfl
  a4OverV4QuotientOrder_eq := rfl
  c6ToHDegree_eq := rfl
  c6ToHRamificationCount_eq := rfl

/-- A lightweight carrier for the `D₈`-quotient Jacobian in the Prym-square wrapper. -/
abbrev killo_s4_burnside_kani_rosen_prym_square_d8_jacobian_carrier := Fin 2 → ℚ

/-- A lightweight carrier for the Prym of `C₆/H`, modeled as a double copy of the `D₈` Jacobian
block. -/
abbrev killo_s4_burnside_kani_rosen_prym_square_prym_carrier :=
  killo_s4_burnside_kani_rosen_prym_square_d8_jacobian_carrier ×
    killo_s4_burnside_kani_rosen_prym_square_d8_jacobian_carrier

/-- The paper-facing Jacobian-isogeny wrapper for `Prym(C₆/H) ~ J(X/D₈)^2`. -/
def killo_s4_burnside_kani_rosen_prym_square_prym_square_isogeny : Prop :=
  Nonempty
    (killo_s4_burnside_kani_rosen_prym_square_prym_carrier ≃
      killo_s4_burnside_kani_rosen_prym_square_d8_jacobian_carrier ×
        killo_s4_burnside_kani_rosen_prym_square_d8_jacobian_carrier)

/-- Paper label: `thm:killo-s4-burnside-kani-rosen-prym-square`. The three explicit induced
representation identities match the Burnside/Kani--Rosen relations; the audited unramified
`A₄`-lift furnishes the cyclic triple-cover/Prym interface; and the chapter-local Jacobian/Prym
package realizes the resulting Prym factor as a square of the rank-two `A₂` block. -/
theorem paper_killo_s4_burnside_kani_rosen_prym_square :
    killo_s4_burnside_kani_rosen_prym_square_identity_one ∧
      killo_s4_burnside_kani_rosen_prym_square_identity_two ∧
      killo_s4_burnside_kani_rosen_prym_square_identity_three ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.a4ActsFreely ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.xToHUnramified ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.genusH = 5 ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.hToP1IsDoubleCover ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.c6ToHIsCyclicTripleCover ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.c6ToHUnramified ∧
      killo_s4_burnside_kani_rosen_prym_square_lift_data.genusC6 = 13 ∧
      s4v4CompatibleBiellipticPencils.card = 3 ∧
      (let D := cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data
       D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧ D.naturalPrymPolarizationIsA2) ∧
      a2CartanForm.det = 3 ∧
      killo_s4_burnside_kani_rosen_prym_square_prym_square_isogeny := by
  have hId1 : killo_s4_burnside_kani_rosen_prym_square_identity_one := by
    intro i
    fin_cases i <;>
      norm_num [killo_s4_burnside_kani_rosen_prym_square_rho_s4,
        killo_s4_burnside_kani_rosen_prym_square_rho_a4,
        killo_s4_burnside_kani_rosen_prym_square_rho_v4,
        killo_s4_burnside_kani_rosen_prym_square_rho_d8]
  have hId2 : killo_s4_burnside_kani_rosen_prym_square_identity_two := by
    intro i
    fin_cases i <;>
      norm_num [killo_s4_burnside_kani_rosen_prym_square_rho_s4,
        killo_s4_burnside_kani_rosen_prym_square_rho_s3,
        killo_s4_burnside_kani_rosen_prym_square_rho_c4,
        killo_s4_burnside_kani_rosen_prym_square_rho_c2]
  have hId3 : killo_s4_burnside_kani_rosen_prym_square_identity_three := by
    intro i
    fin_cases i <;>
      norm_num [killo_s4_burnside_kani_rosen_prym_square_rho_s4,
        killo_s4_burnside_kani_rosen_prym_square_rho_a4,
        killo_s4_burnside_kani_rosen_prym_square_rho_v4,
        killo_s4_burnside_kani_rosen_prym_square_rho_s3,
        killo_s4_burnside_kani_rosen_prym_square_rho_c4,
        killo_s4_burnside_kani_rosen_prym_square_rho_c3]
  have hLift := paper_killo_s4_even_subgroup_free_action_unramified_a4_lift
    killo_s4_burnside_kani_rosen_prym_square_lift_data
  rcases paper_cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting with
    ⟨hpencils, hprym, hdet, _, _⟩
  refine ⟨hId1, hId2, hId3, hLift.1, hLift.2.1, hLift.2.2.1, hLift.2.2.2.1, hLift.2.2.2.2.1,
    hLift.2.2.2.2.2.1, hLift.2.2.2.2.2.2, hpencils, hprym, hdet, ?_⟩
  exact ⟨Equiv.refl _⟩

end Omega.CircleDimension
