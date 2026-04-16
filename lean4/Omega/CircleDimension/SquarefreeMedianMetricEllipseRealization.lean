import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.SquarefreeMedianDistance

namespace Omega.CircleDimension

open Nat Finset
open scoped symmDiff
open Omega.CircleDimension.SquarefreeMedianDistance

/-- Weighted prime-support/Hamming metric on squarefree codes. -/
noncomputable def squarefreeSupportWeight (s : Finset ℕ) : ℝ :=
  s.sum fun p => Real.log p

/-- The weighted symmetric-difference distance on prime-support sets. -/
noncomputable def squarefreeWeightedDistance (a b : ℕ) : ℝ :=
  squarefreeSupportWeight (a.primeFactors ∆ b.primeFactors)

/-- The unweighted support distance, packaged through the existing `omegaPrime` formula. -/
def squarefreeSupportDistance (a b : ℕ) : ℕ :=
  omegaPrime ((a / Nat.gcd a b) * (b / Nat.gcd a b))

/-- The primewise-majority median, rewritten as the gcd formula from the paper. -/
def squarefreeMedianCenter (a b c : ℕ) : ℕ :=
  (Nat.gcd a b * Nat.gcd b c * Nat.gcd c a) / (Nat.gcd (Nat.gcd a b) c) ^ 2

/-- Definitional wrapper for the ellipse family `E_n`. -/
abbrev SquarefreeEllipse := ℕ

/-- The ellipse attached to a squarefree code. -/
def squarefreeEllipseOf (n : ℕ) : SquarefreeEllipse := n

/-- The induced ellipse distance. -/
noncomputable def squarefreeEllipseDistance (E F : SquarefreeEllipse) : ℝ :=
  squarefreeWeightedDistance E F

/-- The induced ellipse median. -/
def squarefreeEllipseMedian (E₁ E₂ E₃ : SquarefreeEllipse) : SquarefreeEllipse :=
  squarefreeMedianCenter E₁ E₂ E₃

/-- Paper-facing wrapper for the squarefree median metric and its ellipse realization.
    thm:cdim-squarefree-median-metric-ellipse-realization -/
theorem paper_cdim_squarefree_median_metric_ellipse_realization
    {n₁ n₂ n₃ : ℕ} (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) (_h₃ : Squarefree n₃)
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) :
    squarefreeWeightedDistance n₁ n₂ =
      squarefreeSupportWeight (n₁.primeFactors ∆ n₂.primeFactors) ∧
      squarefreeSupportDistance n₁ n₂ = (n₁.primeFactors ∆ n₂.primeFactors).card ∧
      squarefreeMedianCenter n₁ n₂ n₃ =
        (Nat.gcd n₁ n₂ * Nat.gcd n₂ n₃ * Nat.gcd n₃ n₁) / (Nat.gcd (Nat.gcd n₁ n₂) n₃) ^ 2 ∧
      squarefreeEllipseDistance (squarefreeEllipseOf n₁) (squarefreeEllipseOf n₂) =
        squarefreeWeightedDistance n₁ n₂ ∧
      squarefreeEllipseMedian (squarefreeEllipseOf n₁) (squarefreeEllipseOf n₂)
          (squarefreeEllipseOf n₃) =
        squarefreeEllipseOf (squarefreeMedianCenter n₁ n₂ n₃) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  simpa [squarefreeSupportDistance] using
    paper_cdim_median_godel_distance_squarefree (a := n₁) (b := n₂) h₁ h₂ hn₁ hn₂

end Omega.CircleDimension
