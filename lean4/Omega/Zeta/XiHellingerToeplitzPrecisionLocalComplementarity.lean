import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-hellinger-toeplitz-precision-local-complementarity`. -/
theorem paper_xi_hellinger_toeplitz_precision_local_complementarity
    (Delta aLoc B leading tail : ℝ) (ha : 0 < aLoc) (hlead : 0 < leading)
    (hDelta : Delta = 2 * aLoc) (hmain : B ≥ 2 * leading / Delta + tail) :
    B ≥ leading / aLoc + tail ∧
      (0 ≤ tail → 1 ≤ (B * aLoc) / leading) := by
  have hterm : 2 * leading / Delta = leading / aLoc := by
    rw [hDelta]
    field_simp [ha.ne']
  have hB : B ≥ leading / aLoc + tail := by
    simpa [hterm] using hmain
  refine ⟨hB, ?_⟩
  intro htail
  have hbase : leading / aLoc ≤ B := by
    linarith
  have hmul : leading ≤ B * aLoc := by
    have hmul' := mul_le_mul_of_nonneg_right hbase ha.le
    simpa [div_mul_cancel₀ leading ha.ne'] using hmul'
  have hdiv := div_le_div_of_nonneg_right hmul hlead.le
  simpa [div_self hlead.ne'] using hdiv

end Omega.Zeta
