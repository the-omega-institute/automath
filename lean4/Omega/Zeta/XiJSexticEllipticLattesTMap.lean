import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- For the quartic-over-cubic Lattès map attached to the discriminant elliptic curve
`y² = (t - 1728)(t² + 1862 t + 161792)`, the three finite branch values `1728, α, β` occur with
double quadratic fibers. -/
theorem paper_xi_j_sextic_elliptic_lattes_three_branch_square_factorization
    (t : ℝ) (ht : t ≠ 1728) (hQ : t ^ 2 + 1862 * t + 161792 ≠ 0) :
    let α : ℝ := -931 - 89 * Real.sqrt 89
    let β : ℝ := -931 + 89 * Real.sqrt 89
    let Q : ℝ := t ^ 2 + 1862 * t + 161792
    let L : ℝ := (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) / (4 * (t - 1728) * Q)
    L - 1728 = (t ^ 2 - 3456 * t - 3379328) ^ 2 / (4 * (t - 1728) * Q) ∧
      L - α =
        (t ^ 2 + (1862 + 178 * Real.sqrt 89) * t + 161792 - 307584 * Real.sqrt 89) ^ 2 /
          (4 * (t - 1728) * Q) ∧
      L - β =
        (t ^ 2 + (1862 - 178 * Real.sqrt 89) * t + 161792 + 307584 * Real.sqrt 89) ^ 2 /
          (4 * (t - 1728) * Q) := by
  have hsqrt89 : (Real.sqrt 89) ^ 2 = (89 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  let N : ℝ := t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272
  let D : ℝ := 4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)
  have ht0 : t - 1728 ≠ 0 := sub_ne_zero.mpr ht
  have hD : D ≠ 0 := by
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h4 ht0) hQ
  have hQinv : t * (t + 1862) + 161792 ≠ 0 := by
    intro h0
    apply hQ
    nlinarith
  have hrewrite1728 : N / D - 1728 = (N - 1728 * D) / D := by
    dsimp [N, D]
    apply (mul_right_cancel₀ hQinv)
    field_simp [hD, hQinv]
  have hrewriteAlpha :
      N / D - (-931 - 89 * Real.sqrt 89) = (N - (-931 - 89 * Real.sqrt 89) * D) / D := by
    dsimp [N, D]
    apply (mul_right_cancel₀ hQinv)
    field_simp [hD, hQinv]
  have hrewriteBeta :
      N / D - (-931 + 89 * Real.sqrt 89) = (N - (-931 + 89 * Real.sqrt 89) * D) / D := by
    dsimp [N, D]
    apply (mul_right_cancel₀ hQinv)
    field_simp [hD, hQinv]
  have hnum1728 : N - 1728 * D = (t ^ 2 - 3456 * t - 3379328) ^ 2 := by
    dsimp [N, D]
    ring_nf
  have hnumAlpha :
      N - (-931 - 89 * Real.sqrt 89) * D =
        (t ^ 2 + (1862 + 178 * Real.sqrt 89) * t + 161792 - 307584 * Real.sqrt 89) ^ 2 := by
    dsimp [N, D]
    ring_nf
    repeat' rw [hsqrt89]
    ring_nf
  have hnumBeta :
      N - (-931 + 89 * Real.sqrt 89) * D =
        (t ^ 2 + (1862 - 178 * Real.sqrt 89) * t + 161792 + 307584 * Real.sqrt 89) ^ 2 := by
    dsimp [N, D]
    ring_nf
    repeat' rw [hsqrt89]
    ring_nf
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · rw [show
        (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
            (4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)) - 1728 =
          N / D - 1728 by rfl]
    rw [hrewrite1728, hnum1728]
  · rw [show
        (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
            (4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)) - (-931 - 89 * Real.sqrt 89) =
          N / D - (-931 - 89 * Real.sqrt 89) by rfl]
    rw [hrewriteAlpha, hnumAlpha]
  · rw [show
        (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
            (4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)) - (-931 + 89 * Real.sqrt 89) =
          N / D - (-931 + 89 * Real.sqrt 89) by rfl]
    rw [hrewriteBeta, hnumBeta]

end Omega.Zeta
