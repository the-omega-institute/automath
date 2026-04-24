import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-integer-anchor-local-convex-interpolation-squeeze`. On each unit
interval, the convex pressure curve lies below the chord through the integer anchors, while the
left and right discrete support-line lower bounds are inherited verbatim. -/
theorem paper_conclusion_integer_anchor_local_convex_interpolation_squeeze
    (Λ : ℝ → ℝ) (β : ℕ → ℝ) (Δminus Δplus : ℕ → ℝ) (q : ℕ)
    (hβleft : Λ (q - 1) = β q) (hβright : Λ q = β (q + 1))
    (hconv : ConvexOn ℝ (Set.Icc (q - 1 : ℝ) q) Λ)
    (hleft : ∀ t ∈ Set.Icc (q - 1 : ℝ) q, β q + (t - (q - 1 : ℝ)) * Δminus q ≤ Λ t)
    (hright : ∀ t ∈ Set.Icc (q - 1 : ℝ) q,
      β (q + 1) - ((q : ℝ) - t) * Δplus (q + 1) ≤ Λ t) :
    ∀ t ∈ Set.Icc (q - 1 : ℝ) q,
      β q + (t - (q - 1 : ℝ)) * Δminus q ≤ Λ t ∧
        Λ t ≤ ((q : ℝ) - t) * β q + (t - (q - 1 : ℝ)) * β (q + 1) ∧
        β (q + 1) - ((q : ℝ) - t) * Δplus (q + 1) ≤ Λ t := by
  intro t ht
  refine ⟨hleft t ht, ?_, hright t ht⟩
  have hqminus1_mem : (q - 1 : ℝ) ∈ Set.Icc (q - 1 : ℝ) q := by
    constructor <;> linarith
  have hq_mem : (q : ℝ) ∈ Set.Icc (q - 1 : ℝ) q := by
    constructor <;> linarith
  have hcoeff_left_nonneg : 0 ≤ (q : ℝ) - t := by
    linarith [ht.2]
  have hcoeff_right_nonneg : 0 ≤ t - (q - 1 : ℝ) := by
    linarith [ht.1]
  have hcoeff_sum : ((q : ℝ) - t) + (t - (q - 1 : ℝ)) = 1 := by
    ring
  have hupper :=
    hconv.2 hqminus1_mem hq_mem hcoeff_left_nonneg hcoeff_right_nonneg hcoeff_sum
  have hpoint :
      (((q : ℝ) - t) • (q - 1 : ℝ) + (t - (q - 1 : ℝ)) • (q : ℝ)) = t := by
    simp [smul_eq_mul]
    ring
  rw [hpoint] at hupper
  simpa [smul_eq_mul, hβleft, hβright] using hupper

end Omega.Conclusion
