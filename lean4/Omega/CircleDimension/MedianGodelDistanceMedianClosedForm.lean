import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic
import Omega.CircleDimension.MedianThetaRigidityPrimeRatio
import Omega.CircleDimension.SquarefreeMedianMetricEllipseRealization

namespace Omega.CircleDimension

open Nat Finset
open scoped symmDiff

/-- Paper-facing package for the median Gödel-distance closed form: `Θ`-class labels are recovered
injectively from their prime supports, the squarefree quotient/product formula computes distance by
prime-support symmetric difference, and the primewise-majority median is the gcd closed form.
    thm:cdim-median-godel-distance-median-closed-form -/
theorem paper_cdim_median_godel_distance_median_closed_form
    (P : PrimeRatioEmbeddingPackage)
    {n₁ n₂ n₃ : ℕ} (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) (h₃ : Squarefree n₃)
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) :
    Function.Injective P.thetaPrime ∧
      squarefreeSupportDistance n₁ n₂ = (n₁.primeFactors ∆ n₂.primeFactors).card ∧
      squarefreeMedianCenter n₁ n₂ n₃ =
        (Nat.gcd n₁ n₂ * Nat.gcd n₂ n₃ * Nat.gcd n₃ n₁) /
          (Nat.gcd (Nat.gcd n₁ n₂) n₃) ^ 2 := by
  have htheta := paper_cdim_median_theta_rigidity_prime_ratio P
  have hmetric :=
    paper_cdim_squarefree_median_metric_ellipse_realization
      (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) h₁ h₂ h₃ hn₁ hn₂
  rcases htheta with ⟨_, _, _, hinjective, _⟩
  rcases hmetric with ⟨_, hdistance, hmedian, _, _⟩
  exact ⟨hinjective, hdistance, hmedian⟩

end Omega.CircleDimension
