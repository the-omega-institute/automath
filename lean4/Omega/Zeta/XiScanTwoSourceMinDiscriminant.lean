import Mathlib.Tactic

namespace Omega.Zeta

open Finset

/-- Paper label: `prop:xi-scan-two-source-min-discriminant`. -/
theorem paper_xi_scan_two_source_min_discriminant (κ : ℕ) (c ρ : Fin κ → ℝ)
    (hc : ∀ j, 0 ≤ c j) :
    ((∑ j : Fin κ, c j) * (∑ j : Fin κ, c j * ρ j ^ 2) -
        (∑ j : Fin κ, c j * ρ j) ^ 2 =
      (1 / 2 : ℝ) *
        (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * (ρ j - ρ k) ^ 2)) ∧
      0 ≤ (∑ j : Fin κ, c j) * (∑ j : Fin κ, c j * ρ j ^ 2) -
        (∑ j : Fin κ, c j * ρ j) ^ 2 := by
  classical
  have hAC :
      (∑ j : Fin κ, c j) * (∑ j : Fin κ, c j * ρ j ^ 2) =
        ∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ k ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  have hBB :
      (∑ j : Fin κ, c j * ρ j) ^ 2 =
        ∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ j * ρ k := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  have hSym :
      (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ j ^ 2) =
        ∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ k ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  have hId :
      (∑ j : Fin κ, c j) * (∑ j : Fin κ, c j * ρ j ^ 2) -
          (∑ j : Fin κ, c j * ρ j) ^ 2 =
        (1 / 2 : ℝ) *
          (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * (ρ j - ρ k) ^ 2) := by
    rw [hAC, hBB]
    rw [show
        (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ k ^ 2) -
            (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ j * ρ k) =
          ∑ j : Fin κ, ∑ k : Fin κ,
            (c j * c k * ρ k ^ 2 - c j * c k * ρ j * ρ k) by
        simp [Finset.sum_sub_distrib]]
    rw [show
        (1 / 2 : ℝ) *
            (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * (ρ j - ρ k) ^ 2) =
          (1 / 2 : ℝ) *
            (∑ j : Fin κ, ∑ k : Fin κ,
              (c j * c k * ρ j ^ 2 - 2 * (c j * c k * ρ j * ρ k) +
                c j * c k * ρ k ^ 2)) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro j hj
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring]
    have hCross :
        (∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ j * ρ k) =
          ∑ j : Fin κ, ∑ k : Fin κ, c j * c k * ρ k * ρ j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hSym]
    ring_nf
    let S : ℝ := ∑ x : Fin κ, ∑ x_1 : Fin κ, c x * c x_1 * ρ x_1 ^ 2
    let T : ℝ := ∑ x : Fin κ, ∑ x_1 : Fin κ, c x * c x_1 * ρ x * ρ x_1
    let U : ℝ := ∑ x : Fin κ, ∑ x_1 : Fin κ, c x * c x_1 * ρ x * ρ x_1 * 2
    change S - T = S + U * (-1 / 2)
    have hU : U = T * 2 := by
      simp [U, T, Finset.sum_mul]
    rw [hU]
    ring
  constructor
  · exact hId
  · rw [hId]
    apply mul_nonneg
    · norm_num
    · refine Finset.sum_nonneg ?_
      intro j hj
      refine Finset.sum_nonneg ?_
      intro k hk
      exact mul_nonneg (mul_nonneg (hc j) (hc k)) (sq_nonneg (ρ j - ρ k))

end Omega.Zeta
