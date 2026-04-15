import Mathlib.Tactic

namespace Omega.Folding.PeriodicCompressionRatio

/-- Periodic compression ratio.
    cor:Ym-periodic-compression-ratio -/
def compressionRatio (a b : ℕ) : ℕ := b / a

/-- `1 ≤ b/a` when `0 < a ≤ b`.
    cor:Ym-periodic-compression-ratio -/
theorem one_le_div_of_le (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    1 ≤ b / a := (Nat.one_le_div_iff ha).mpr hab

/-- `b/a ≤ S` when `b ≤ S·a` and `0 < a`.
    cor:Ym-periodic-compression-ratio -/
theorem div_le_of_le_mul (a b S : ℕ) (ha : 0 < a) (hbS : b ≤ S * a) :
    b / a ≤ S := by
  have hdiv : b / a ≤ (S * a) / a := Nat.div_le_div_right hbS
  rw [Nat.mul_div_cancel _ ha] at hdiv
  exact hdiv

/-- Compression ratio is in `[1, S]`.
    cor:Ym-periodic-compression-ratio -/
theorem compressionRatio_bound (a b S : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hbS : b ≤ S * a) :
    1 ≤ compressionRatio a b ∧ compressionRatio a b ≤ S := by
  unfold compressionRatio
  exact ⟨one_le_div_of_le a b ha hab, div_le_of_le_mul a b S ha hbS⟩

/-- Paper package: `Y_m` periodic compression ratio bound.
    cor:Ym-periodic-compression-ratio -/
theorem paper_Ym_periodic_compression_ratio (a b S : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (hbS : b ≤ S * a) :
    1 ≤ compressionRatio a b ∧ compressionRatio a b ≤ S :=
  compressionRatio_bound a b S ha hab hbS

end Omega.Folding.PeriodicCompressionRatio
