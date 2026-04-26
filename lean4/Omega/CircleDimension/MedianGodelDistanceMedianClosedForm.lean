import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic
import Omega.CircleDimension.MobiusBipartiteColoring
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

/-- Paper label: `cor:cdim-median-mobius-bipartite-coloring`. Distance one in the squarefree
support graph flips the parity of the number of prime factors, hence flips the Möbius sign. -/
theorem paper_cdim_median_mobius_bipartite_coloring {u v : ℕ} (hu : Squarefree u)
    (hv : Squarefree v) (hedge : squarefreeSupportDistance u v = 1) :
    (-1 : ℤ) ^ u.primeFactors.card = -((-1 : ℤ) ^ v.primeFactors.card) := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := hv.ne_zero
  let A := u.primeFactors
  let B := v.primeFactors
  have hdistance : squarefreeSupportDistance u v = (A ∆ B).card := by
    simpa [A, B, squarefreeSupportDistance] using
      Omega.CircleDimension.SquarefreeMedianDistance.paper_cdim_median_godel_distance_squarefree
        (a := u) (b := v) hu hv hu0 hv0
  have hsymm : ((A \ B) ∪ (B \ A)).card = 1 := by
    have hcard : (A ∆ B).card = 1 := by omega
    simpa [A, B, symmDiff_def, Finset.sup_eq_union] using hcard
  have hsum : (A \ B).card + (B \ A).card = 1 := by
    have hunion :
        ((A \ B) ∪ (B \ A)).card = (A \ B).card + (B \ A).card := by
      simpa using
        (Finset.card_union_of_disjoint (s := A \ B) (t := B \ A) disjoint_sdiff_sdiff)
    omega
  have hcases :
      ((A \ B).card = 1 ∧ (B \ A).card = 0) ∨ ((A \ B).card = 0 ∧ (B \ A).card = 1) := by
    omega
  rcases hcases with hAB | hBA
  · rcases hAB with ⟨hAB, hBA⟩
    have hAcard : A.card = B.card + 1 := by
      have hA' : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have hB' : (B \ A).card + (A ∩ B).card = B.card := by
        simpa [Finset.inter_comm] using (Finset.card_sdiff_add_card_inter B A)
      omega
    have hcard : u.primeFactors.card = v.primeFactors.card + 1 := by
      simpa [A, B] using hAcard
    rw [hcard, Omega.CircleDimension.MobiusBipartiteColoring.neg_one_pow_succ]
  · rcases hBA with ⟨hAB, hBA⟩
    have hBcard : B.card = A.card + 1 := by
      have hA' : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have hB' : (B \ A).card + (A ∩ B).card = B.card := by
        simpa [Finset.inter_comm] using (Finset.card_sdiff_add_card_inter B A)
      omega
    have hcard : v.primeFactors.card = u.primeFactors.card + 1 := by
      simpa [A, B] using hBcard
    rw [hcard, Omega.CircleDimension.MobiusBipartiteColoring.neg_one_pow_succ]
    simp

end Omega.CircleDimension
