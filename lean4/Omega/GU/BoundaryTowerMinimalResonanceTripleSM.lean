import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.ZeckendorfCountClosure

namespace Omega.GU

/-- Concrete boundary-tower data for the minimal-resonance triple. The boundary triple itself is
recorded numerically, the selected Zeckendorf/Fibonacci boundary indices identify the isomorphism
class, and the Lie dimension is then read off from that selected triple. -/
structure BoundaryTowerMinimalResonanceTripleSMData where
  boundaryTriple : ℕ × ℕ × ℕ
  selectedBoundaryIndices : ℕ × ℕ × ℕ
  lieDimension : ℕ
  classifyBoundaryTriple :
    boundaryTriple = (Nat.fib 2, Nat.fib 4, Nat.fib 6) →
      selectedBoundaryIndices = (2, 4, 6)
  identifyStandardModel :
    selectedBoundaryIndices = (2, 4, 6) →
      lieDimension = Nat.fib 2 + Nat.fib 4 + Nat.fib 6

namespace BoundaryTowerMinimalResonanceTripleSMData

/-- The minimal-resonance triple determines the unique boundary-tower isomorphism class. -/
def uniqueIsomorphismClass (D : BoundaryTowerMinimalResonanceTripleSMData) : Prop :=
  D.selectedBoundaryIndices = (2, 4, 6)

/-- The selected boundary triple has the Standard-Model Lie dimension `12`. -/
def isStandardModelLieAlgebra (D : BoundaryTowerMinimalResonanceTripleSMData) : Prop :=
  D.lieDimension = 12

end BoundaryTowerMinimalResonanceTripleSMData

/-- Paper-facing wrapper for the minimal-resonance boundary triple: the audited Fibonacci values
`1, 3, 8` identify the triple with `(F₂, F₄, F₆)`, the local classification assumptions then pin
down the unique isomorphism class, and the existing Standard-Model signature sum forces Lie
dimension `12`.
    cor:bdry-tower-minimal-resonance-triple-sm -/
theorem paper_bdry_tower_minimal_resonance_triple_sm
    (D : BoundaryTowerMinimalResonanceTripleSMData) :
    D.boundaryTriple = (1, 3, 8) → D.uniqueIsomorphismClass ∧ D.isStandardModelLieAlgebra := by
  intro hTriple
  have hSig := paper_gu_sm_signature_union
  have hfib2 : Nat.fib 2 = 1 := hSig.1.symm
  have hfib4 : Nat.fib 4 = 3 := hSig.2.1.symm
  have hfib6 : Nat.fib 6 = 8 := hSig.2.2.1.symm
  have hFibTriple : D.boundaryTriple = (Nat.fib 2, Nat.fib 4, Nat.fib 6) := by
    calc
      D.boundaryTriple = (1, 3, 8) := hTriple
      _ = (Nat.fib 2, Nat.fib 4, Nat.fib 6) := by simpa [hfib2, hfib4, hfib6]
  have hClass : D.selectedBoundaryIndices = (2, 4, 6) := D.classifyBoundaryTriple hFibTriple
  have hDimFib : D.lieDimension = Nat.fib 2 + Nat.fib 4 + Nat.fib 6 :=
    D.identifyStandardModel hClass
  have hDimTwelve : D.lieDimension = 12 := by
    calc
      D.lieDimension = Nat.fib 2 + Nat.fib 4 + Nat.fib 6 := hDimFib
      _ = 12 := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hSig.2.2.2.2.1.symm
  exact ⟨hClass, hDimTwelve⟩

end Omega.GU
