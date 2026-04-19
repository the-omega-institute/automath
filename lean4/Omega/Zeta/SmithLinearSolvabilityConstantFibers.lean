import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite package for a Smith-diagonalized system modulo `b`. Admissible targets are
exactly the coordinatewise divisible ones, and each admissible fiber is explicitly equivalent to
the free-kernel block times the per-coordinate gcd choices. -/
structure SmithLinearSolvabilityPackage where
  m : ℕ
  n : ℕ
  b : ℕ
  diagonal : Fin m → ℕ
  solution : (Fin m → ZMod b) → Type
  instSolutionFintype : ∀ y, Fintype (solution y)
  coordinateDivisibility : (Fin m → ZMod b) → Prop
  solvable_of_divisibility :
    ∀ y, coordinateDivisibility y → Nonempty (solution y)
  divisibility_of_solvable :
    ∀ y, Nonempty (solution y) → coordinateDivisibility y
  solutionEquiv :
    ∀ y, coordinateDivisibility y →
      solution y ≃ (Fin (b ^ (n - m)) × ∀ i : Fin m, Fin (Nat.gcd (diagonal i) b))
  imageCardinality : ℕ
  imageEquiv :
    {y : Fin m → ZMod b // coordinateDivisibility y} ≃ Fin imageCardinality
  imageCardinality_eq :
    imageCardinality = b ^ m / ∏ i : Fin m, Nat.gcd (diagonal i) b

attribute [instance] SmithLinearSolvabilityPackage.instSolutionFintype

namespace SmithLinearSolvabilityPackage

/-- A Smith-diagonalized system is solvable exactly on the coordinatewise divisible targets. -/
def solvableIffCoordinateDivisibility (P : SmithLinearSolvabilityPackage) : Prop :=
  ∀ y : Fin P.m → ZMod P.b, P.coordinateDivisibility y ↔ Nonempty (P.solution y)

/-- Every admissible fiber has the expected constant cardinality
`b^(n-m) * ∏ gcd(d_i, b)`. -/
def constantFiberCardinality (P : SmithLinearSolvabilityPackage) : Prop :=
  ∀ y : Fin P.m → ZMod P.b,
    P.coordinateDivisibility y →
      Nat.card (P.solution y) =
        P.b ^ (P.n - P.m) * ∏ i : Fin P.m, Nat.gcd (P.diagonal i) P.b

/-- The admissible targets form the image, whose size is the expected quotient
`b^m / ∏ gcd(d_i, b)`. -/
def imageCardinalityFormula (P : SmithLinearSolvabilityPackage) : Prop :=
  Nat.card {y : Fin P.m → ZMod P.b // P.coordinateDivisibility y} =
    P.b ^ P.m / ∏ i : Fin P.m, Nat.gcd (P.diagonal i) P.b

end SmithLinearSolvabilityPackage

open SmithLinearSolvabilityPackage

/-- The Smith-diagonal finite package yields the coordinatewise solvability criterion, the
constant admissible fiber size, and the resulting image-cardinality formula.
    thm:xi-time-part53ac-smith-linear-solvability-constant-fibers -/
theorem paper_xi_time_part53ac_smith_linear_solvability_constant_fibers
    (P : SmithLinearSolvabilityPackage) :
    SmithLinearSolvabilityPackage.solvableIffCoordinateDivisibility P ∧
      SmithLinearSolvabilityPackage.constantFiberCardinality P ∧
      SmithLinearSolvabilityPackage.imageCardinalityFormula P := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · exact P.solvable_of_divisibility y
    · exact P.divisibility_of_solvable y
  · intro y hy
    calc
      Nat.card (P.solution y)
          = Nat.card (Fin (P.b ^ (P.n - P.m)) ×
              ((i : Fin P.m) → Fin (Nat.gcd (P.diagonal i) P.b))) := by
              exact Nat.card_congr (P.solutionEquiv y hy)
      _ = P.b ^ (P.n - P.m) * ∏ i : Fin P.m, Nat.gcd (P.diagonal i) P.b := by
            rw [Nat.card_prod, Nat.card_fin, Nat.card_pi]
            simp
  · calc
      Nat.card {y : Fin P.m → ZMod P.b // P.coordinateDivisibility y}
          = Nat.card (Fin P.imageCardinality) := by
              exact Nat.card_congr P.imageEquiv
      _ = P.imageCardinality := by simp
      _ = P.b ^ P.m / ∏ i : Fin P.m, Nat.gcd (P.diagonal i) P.b := P.imageCardinality_eq

end Omega.Zeta
