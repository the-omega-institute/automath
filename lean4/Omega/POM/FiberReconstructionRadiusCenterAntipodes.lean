import Mathlib.Tactic
import Omega.POM.FibCubeAntipodeCount

namespace Omega.POM

/-- Radius contribution of a path component `P_ℓ`, written as `⌈ℓ / 2⌉ = (ℓ + 1) / 2`. -/
def fibPathRadius (ℓ : ℕ) : ℕ :=
  (ℓ + 1) / 2

/-- Number of graph centers in a path component `P_ℓ`. -/
def fibPathCenterCount (ℓ : ℕ) : ℕ :=
  if Even ℓ then 1 else 2

/-- Radius of the Cartesian-product fiber reconstruction graph. -/
def fiberReconstructionRadius : List ℕ → ℕ
  | [] => 0
  | ℓ :: lengths => fibPathRadius ℓ + fiberReconstructionRadius lengths

/-- Center count of the Cartesian-product fiber reconstruction graph. -/
def fiberReconstructionCenterCount : List ℕ → ℕ
  | [] => 1
  | ℓ :: lengths => fibPathCenterCount ℓ * fiberReconstructionCenterCount lengths

/-- Total count of even zero segments across all Fibonacci-cube factors. -/
def fiberReconstructionEvenExponent : List (List ℕ) → ℕ
  | [] => 0
  | segments :: rest => evenZeroSegmentCount segments + fiberReconstructionEvenExponent rest

/-- Antipode count in the Cartesian product, obtained by multiplying the Fibonacci-cube factors. -/
def fiberReconstructionAntipodeCount : List (List ℕ) → ℕ
  | [] => 1
  | segments :: rest => zeroSegmentPhaseChoices segments * fiberReconstructionAntipodeCount rest

/-- Antipode counts factor across the Cartesian-product decomposition. -/
private theorem fiberReconstructionAntipodeCount_eq_pow :
    ∀ segments : List (List ℕ),
      fiberReconstructionAntipodeCount segments = 2 ^ fiberReconstructionEvenExponent segments
  | [] => by simp [fiberReconstructionAntipodeCount, fiberReconstructionEvenExponent]
  | segments :: rest => by
      calc
        fiberReconstructionAntipodeCount (segments :: rest)
            = zeroSegmentPhaseChoices segments * fiberReconstructionAntipodeCount rest := by
                rfl
        _ = 2 ^ evenZeroSegmentCount segments * 2 ^ fiberReconstructionEvenExponent rest := by
              rw [paper_pom_fibcube_antipode_count, fiberReconstructionAntipodeCount_eq_pow rest]
        _ = 2 ^ (evenZeroSegmentCount segments + fiberReconstructionEvenExponent rest) := by
              rw [pow_add]
        _ = 2 ^ fiberReconstructionEvenExponent (segments :: rest) := by
              rfl

/-- Paper-facing wrapper for the Cartesian-product fiber reconstruction graph:
    radii add, centers multiply componentwise, and antipode counts factor through the Fibonacci-cube
    zero-segment exponent.
    thm:pom-fiber-reconstruction-radius-center-antipodes -/
theorem paper_pom_fiber_reconstruction_radius_center_antipodes
    (lengths : List ℕ) (segments : List (List ℕ)) :
    fiberReconstructionRadius lengths = (lengths.map fibPathRadius).sum ∧
      fiberReconstructionCenterCount lengths = (lengths.map fibPathCenterCount).prod ∧
      fiberReconstructionAntipodeCount segments = 2 ^ fiberReconstructionEvenExponent segments := by
  refine ⟨?_, ?_, fiberReconstructionAntipodeCount_eq_pow segments⟩
  · induction lengths with
    | nil =>
        simp [fiberReconstructionRadius]
    | cons ℓ lengths ih =>
        simp [fiberReconstructionRadius, ih, fibPathRadius, Nat.add_comm]
  · induction lengths with
    | nil =>
        simp [fiberReconstructionCenterCount]
    | cons ℓ lengths ih =>
        simp [fiberReconstructionCenterCount, ih, fibPathCenterCount, Nat.mul_comm]

end Omega.POM
