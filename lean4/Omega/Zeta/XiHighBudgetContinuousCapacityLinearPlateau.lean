import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-high-budget-continuous-capacity-linear-plateau`. -/
theorem paper_xi_high_budget_continuous_capacity_linear_plateau
    (C K R : ℕ → ℝ) (β g r : ℝ)
    (hlower : ∀ m, K m * Real.exp (β * (m : ℝ)) ≤ C m)
    (hupper : ∀ m, C m ≤ K m * Real.exp (β * (m : ℝ)) + R m)
    (hK : ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N →
      Real.exp ((g - ε) * (m : ℝ)) ≤ K m ∧
        K m ≤ Real.exp ((g + ε) * (m : ℝ)))
    (hR : ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N →
      R m ≤ Real.exp ((r + ε) * (m : ℝ)))
    (hdom : r < g + β) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N →
      Real.exp ((g + β - ε) * (m : ℝ)) ≤ C m ∧
        C m ≤ 2 * Real.exp ((g + β + ε) * (m : ℝ)) := by
  intro ε hε
  obtain ⟨NK, hNK⟩ := hK ε hε
  let η : ℝ := (g + β - r + ε) / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  obtain ⟨NR, hNR⟩ := hR η hη_pos
  refine ⟨max NK NR, ?_⟩
  intro m hm
  have hmK : NK ≤ m := le_trans (Nat.le_max_left NK NR) hm
  have hmR : NR ≤ m := le_trans (Nat.le_max_right NK NR) hm
  obtain ⟨hK_lower, hK_upper⟩ := hNK m hmK
  have hR_upper := hNR m hmR
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  constructor
  · have hmul :
        Real.exp ((g - ε) * (m : ℝ)) * Real.exp (β * (m : ℝ)) ≤
          K m * Real.exp (β * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hK_lower (le_of_lt (Real.exp_pos _))
    calc
      Real.exp ((g + β - ε) * (m : ℝ))
          = Real.exp ((g - ε) * (m : ℝ)) * Real.exp (β * (m : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
              ring
      _ ≤ K m * Real.exp (β * (m : ℝ)) := hmul
      _ ≤ C m := hlower m
  · have hmain :
        K m * Real.exp (β * (m : ℝ)) ≤
          Real.exp ((g + β + ε) * (m : ℝ)) := by
      calc
        K m * Real.exp (β * (m : ℝ))
            ≤ Real.exp ((g + ε) * (m : ℝ)) * Real.exp (β * (m : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hK_upper (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((g + β + ε) * (m : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
              ring
    have hη_le : r + η ≤ g + β + ε := by
      dsimp [η]
      linarith
    have hR_exp :
        Real.exp ((r + η) * (m : ℝ)) ≤ Real.exp ((g + β + ε) * (m : ℝ)) := by
      exact Real.exp_monotone (mul_le_mul_of_nonneg_right hη_le hm_nonneg)
    calc
      C m ≤ K m * Real.exp (β * (m : ℝ)) + R m := hupper m
      _ ≤ Real.exp ((g + β + ε) * (m : ℝ)) +
            Real.exp ((g + β + ε) * (m : ℝ)) := by
              exact add_le_add hmain (le_trans hR_upper hR_exp)
      _ = 2 * Real.exp ((g + β + ε) * (m : ℝ)) := by ring

end Omega.Zeta
