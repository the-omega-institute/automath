import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- Sizes of the `±1` eigenspaces attached to a fiberwise involution with total size `d` and
fixed-point count `fix`. -/
def trPlusSize (d fix : ℕ) : ℕ := (d + fix) / 2

/-- The `-1` eigenspace size attached to a fiberwise involution with total size `d` and
fixed-point count `fix`. -/
def trMinusSize (d fix : ℕ) : ℕ := (d - fix) / 2

/-- Fiberwise arithmetic form of the time-reversal invariant dimension count.
    cor:op-algebra-time-reversal-invariant-dimension -/
theorem paper_op_algebra_time_reversal_invariant_dimension {ι : Type*} [Fintype ι]
    (d fix : ι → ℕ) (hfix : ∀ x, fix x ≤ d x) (hparity : ∀ x, Even (d x - fix x)) :
    ∑ x, (((d x + fix x) / 2)^2 + ((d x - fix x) / 2)^2) =
      ∑ x, (d x ^ 2 + fix x ^ 2) / 2 := by
  classical
  refine Finset.sum_congr rfl ?_
  intro x hx
  rcases hparity x with ⟨k, hk⟩
  have hle := hfix x
  have hd : d x = fix x + 2 * k := by
    omega
  have hsum : (d x + fix x) / 2 = fix x + k := by
    rw [hd]
    calc
      (fix x + 2 * k + fix x) / 2 = (2 * (fix x + k)) / 2 := by
        ring_nf
      _ = fix x + k := by
        simp
  have hdiff : (d x - fix x) / 2 = k := by
    rw [hd]
    calc
      (fix x + 2 * k - fix x) / 2 = (2 * k) / 2 := by
        omega
      _ = k := by
        simp
  rw [hsum, hdiff, hd]
  have hdouble : (fix x + 2 * k) ^ 2 + fix x ^ 2 = 2 * ((fix x + k) ^ 2 + k ^ 2) := by
    ring
  calc
    (fix x + k) ^ 2 + k ^ 2 = (2 * ((fix x + k) ^ 2 + k ^ 2)) / 2 := by
      simp
    _ = ((fix x + 2 * k) ^ 2 + fix x ^ 2) / 2 := by
      rw [hdouble]

/-- Arithmetic Wedderburn package for a time-reversal involution: after splitting the underlying
fiber into fixed points and `2`-cycles, the plus/minus block sizes are determined by
`(d ± fix) / 2`, and the corresponding centralizer dimension is the expected quadratic average.
    thm:op-algebra-time-reversal-invariant-wedderburn -/
theorem paper_op_algebra_time_reversal_invariant_wedderburn (d fix : ℕ)
    (hfix : fix ≤ d) (hparity : Even (d - fix)) :
    ∃ t, d = fix + 2 * t ∧
      trPlusSize d fix = fix + t ∧
      trMinusSize d fix = t ∧
      trPlusSize d fix + trMinusSize d fix = d ∧
      trPlusSize d fix ^ 2 + trMinusSize d fix ^ 2 = (d ^ 2 + fix ^ 2) / 2 := by
  rcases hparity with ⟨t, ht⟩
  have hd : d = fix + 2 * t := by
    omega
  have hsum : trPlusSize d fix = fix + t := by
    rw [trPlusSize, hd]
    calc
      (fix + 2 * t + fix) / 2 = (2 * (fix + t)) / 2 := by ring_nf
      _ = fix + t := by simp
  have hdiff : trMinusSize d fix = t := by
    rw [trMinusSize, hd]
    calc
      (fix + 2 * t - fix) / 2 = (2 * t) / 2 := by omega
      _ = t := by simp
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · exact hd
  · exact hsum
  · exact hdiff
  · rw [hsum, hdiff, hd]
    ring
  · rw [hsum, hdiff]
    have hdouble : (fix + 2 * t) ^ 2 + fix ^ 2 = 2 * ((fix + t) ^ 2 + t ^ 2) := by
      ring
    calc
      (fix + t) ^ 2 + t ^ 2 = (2 * ((fix + t) ^ 2 + t ^ 2)) / 2 := by simp
      _ = ((fix + 2 * t) ^ 2 + fix ^ 2) / 2 := by rw [hdouble]
      _ = (d ^ 2 + fix ^ 2) / 2 := by rw [hd]

end Omega.OperatorAlgebra
