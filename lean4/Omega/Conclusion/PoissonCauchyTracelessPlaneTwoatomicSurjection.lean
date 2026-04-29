import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-poisson-cauchy-traceless-plane-twoatomic-surjection`. Every
traceless quadrupole pair `(A, B)` is realized by a two-atom parameter pair `(u, v)` with
`u^2 - v^2 = A` and `u v = B`. -/
theorem paper_conclusion_poisson_cauchy_traceless_plane_twoatomic_surjection (A B : ℝ) :
    ∃ u v : ℝ, u ^ 2 - v ^ 2 = A ∧ u * v = B := by
  let R : ℝ := Real.sqrt (A ^ 2 + 4 * B ^ 2)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact Real.sqrt_nonneg _
  have hR_sq : R ^ 2 = A ^ 2 + 4 * B ^ 2 := by
    dsimp [R]
    rw [Real.sq_sqrt]
    positivity
  have hA_sq_le : A ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg B, hR_sq]
  have habsA : |A| ≤ R := by
    have habs : |A| ≤ |R| := sq_le_sq.1 hA_sq_le
    simpa [abs_of_nonneg hR_nonneg] using habs
  rcases abs_le.mp habsA with ⟨hA_lo, hA_hi⟩
  have hRp_nonneg : 0 ≤ R + A := by
    linarith
  have hRm_nonneg : 0 ≤ R - A := by
    linarith
  have hRp_half_nonneg : 0 ≤ (R + A) / 2 := by
    positivity
  have hRm_half_nonneg : 0 ≤ (R - A) / 2 := by
    positivity
  have hmul_halves : ((R + A) / 2) * ((R - A) / 2) = B ^ 2 := by
    nlinarith [hR_sq]
  by_cases hB : 0 ≤ B
  · refine ⟨Real.sqrt ((R + A) / 2), Real.sqrt ((R - A) / 2), ?_, ?_⟩
    · calc
        (Real.sqrt ((R + A) / 2)) ^ 2 - (Real.sqrt ((R - A) / 2)) ^ 2 =
            (R + A) / 2 - (R - A) / 2 := by
              rw [Real.sq_sqrt hRp_half_nonneg, Real.sq_sqrt hRm_half_nonneg]
        _ = A := by
          ring
    · calc
        Real.sqrt ((R + A) / 2) * Real.sqrt ((R - A) / 2) =
            Real.sqrt (((R + A) / 2) * ((R - A) / 2)) := by
              rw [← Real.sqrt_mul hRp_half_nonneg]
        _ = Real.sqrt (B ^ 2) := by
          rw [hmul_halves]
        _ = |B| := by
          rw [Real.sqrt_sq_eq_abs]
        _ = B := by
          rw [abs_of_nonneg hB]
  · have hB_nonpos : B ≤ 0 := le_of_not_ge hB
    refine ⟨Real.sqrt ((R + A) / 2), -Real.sqrt ((R - A) / 2), ?_, ?_⟩
    · calc
        (Real.sqrt ((R + A) / 2)) ^ 2 - (-Real.sqrt ((R - A) / 2)) ^ 2 =
            (R + A) / 2 - (R - A) / 2 := by
              have hneg_sqrt_sq : (-Real.sqrt ((R - A) / 2)) ^ 2 = (R - A) / 2 := by
                nlinarith [Real.sq_sqrt hRm_half_nonneg]
              rw [Real.sq_sqrt hRp_half_nonneg, hneg_sqrt_sq]
        _ = A := by
          ring
    · have hprod_abs :
          Real.sqrt ((R + A) / 2) * Real.sqrt ((R - A) / 2) = -B := by
        calc
          Real.sqrt ((R + A) / 2) * Real.sqrt ((R - A) / 2) =
              Real.sqrt (((R + A) / 2) * ((R - A) / 2)) := by
                rw [← Real.sqrt_mul hRp_half_nonneg]
          _ = Real.sqrt (B ^ 2) := by
            rw [hmul_halves]
          _ = |B| := by
            rw [Real.sqrt_sq_eq_abs]
          _ = -B := by
            rw [abs_of_nonpos hB_nonpos]
      calc
        Real.sqrt ((R + A) / 2) * (-Real.sqrt ((R - A) / 2)) =
            -(Real.sqrt ((R + A) / 2) * Real.sqrt ((R - A) / 2)) := by
              ring
        _ = -(-B) := by
          rw [hprod_abs]
        _ = B := by
          ring

end
end Omega.Conclusion
