import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-entropy-gap-rankone-negative-collapse`. -/
theorem paper_conclusion_entropy_gap_rankone_negative_collapse {k : ℕ} {S g C : ℝ}
    (hS : 0 < S) (hg : 0 ≤ g) (hC : 0 ≤ C) (σ lam : Fin (k + 1) → ℝ)
    (hσ1 : |σ 0 - 4 * Real.pi * S| ≤ C * g)
    (hσtail : ∀ j : Fin (k + 1), j ≠ 0 → |σ j| ≤ C * g)
    (hlam : ∀ j, lam j = - (σ j)^2) :
    |lam 0 + (4 * Real.pi * S)^2| ≤ (8 * Real.pi * S * C + C^2 * g) * g ∧
      ∀ j : Fin (k + 1), j ≠ 0 → |lam j| ≤ C^2 * g^2 := by
  have hpi_nonneg : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hA_nonneg : 0 ≤ 4 * Real.pi * S := by positivity
  constructor
  · set A : ℝ := 4 * Real.pi * S
    have hδ : |σ 0 - A| ≤ C * g := by simpa [A] using hσ1
    have hCg_nonneg : 0 ≤ C * g := mul_nonneg hC hg
    have hδ_nonneg : 0 ≤ |σ 0 - A| := abs_nonneg _
    have hsum_bound : |σ 0 + A| ≤ C * g + 2 * A := by
      calc
        |σ 0 + A| = |(σ 0 - A) + 2 * A| := by ring_nf
        _ ≤ |σ 0 - A| + |2 * A| := abs_add_le _ _
        _ ≤ C * g + 2 * A := by
          have htwoA : |2 * A| = 2 * A := by
            rw [abs_of_nonneg]
            nlinarith
          nlinarith
    have hprod :
        |σ 0 - A| * |σ 0 + A| ≤ C * g * (C * g + 2 * A) :=
      mul_le_mul hδ hsum_bound (abs_nonneg _) hCg_nonneg
    have habs_eq : |lam 0 + A^2| = |σ 0 - A| * |σ 0 + A| := by
      rw [hlam 0]
      calc
        |-σ 0 ^ 2 + A ^ 2| = |(A - σ 0) * (σ 0 + A)| := by ring_nf
        _ = |A - σ 0| * |σ 0 + A| := abs_mul _ _
        _ = |σ 0 - A| * |σ 0 + A| := by rw [abs_sub_comm]
    rw [habs_eq]
    calc
      |σ 0 - A| * |σ 0 + A| ≤ C * g * (C * g + 2 * A) := hprod
      _ = (8 * Real.pi * S * C + C ^ 2 * g) * g := by
        rw [show A = 4 * Real.pi * S by rfl]
        ring
  · intro j hj
    have htail := hσtail j hj
    have hCg_nonneg : 0 ≤ C * g := mul_nonneg hC hg
    have hsq : |σ j| ^ 2 ≤ (C * g) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hCg_nonneg).mpr htail
    calc
      |lam j| = |σ j| ^ 2 := by
        rw [hlam j]
        rw [abs_neg, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      _ ≤ (C * g) ^ 2 := hsq
      _ = C ^ 2 * g ^ 2 := by ring

end Omega.Conclusion
