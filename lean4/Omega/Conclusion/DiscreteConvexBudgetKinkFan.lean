import Mathlib.Data.Real.Basic
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Tactic

namespace Omega.Conclusion

private lemma conclusion_discrete_convex_budget_kink_fan_slope_mono
    (Q : ℕ) (b : ℕ → ℝ)
    (hconv : ∀ r : ℕ, 2 < r → r < Q → b r - b (r - 1) ≤ b (r + 1) - b r) :
    MonotoneOn (fun r : ℕ => b r - b (r - 1)) (Set.Icc 3 Q) := by
  refine monotoneOn_of_le_succ Set.ordConnected_Icc ?_
  intro r _ hr hsucc
  have hrTwo : 2 < r := lt_of_lt_of_le (by decide : 2 < 3) hr.1
  have hrQ : r < Q := Nat.lt_of_succ_le hsucc.2
  simpa [Nat.succ_eq_add_one] using hconv r hrTwo hrQ

/-- Paper label: `thm:conclusion-discrete-convex-budget-kink-fan`. -/
theorem paper_conclusion_discrete_convex_budget_kink_fan (Q q : ℕ) (b : ℕ → ℝ) (γ : ℝ)
    (hq : 2 < q) (hqQ : q < Q)
    (hconv : ∀ r : ℕ, 2 < r → r < Q → b r - b (r - 1) ≤ b (r + 1) - b r) :
    ((∀ r : ℕ, 2 ≤ r → r ≤ Q -> ((r - 1 : ℝ) * γ - b r) ≤ ((q - 1 : ℝ) * γ - b q)) ↔
      (b q - b (q - 1) ≤ γ ∧ γ ≤ b (q + 1) - b q)) := by
  let F : ℕ → ℝ := fun r => ((r - 1 : ℝ) * γ - b r)
  have hSlopeMono :
      MonotoneOn (fun r : ℕ => b r - b (r - 1)) (Set.Icc 3 Q) :=
    conclusion_discrete_convex_budget_kink_fan_slope_mono Q b hconv
  constructor
  · intro hMax
    constructor
    · have hPrevTwo : 2 ≤ q - 1 := by omega
      have hPrevQ : q - 1 ≤ Q := by omega
      have hPrev : F (q - 1) ≤ F q := hMax (q - 1) hPrevTwo hPrevQ
      have hPrevDiff : 0 ≤ F q - F (q - 1) := sub_nonneg.mpr hPrev
      have hPrevEq : F q - F (q - 1) = γ - (b q - b (q - 1)) := by
        have hqOne : 1 ≤ q := by omega
        simp [F, Nat.cast_sub hqOne]
        ring
      rw [hPrevEq] at hPrevDiff
      linarith
    · have hNextTwo : 2 ≤ q + 1 := by omega
      have hNextQ : q + 1 ≤ Q := by omega
      have hNext : F (q + 1) ≤ F q := hMax (q + 1) hNextTwo hNextQ
      have hNextDiff : 0 ≤ F q - F (q + 1) := sub_nonneg.mpr hNext
      have hNextEq : F q - F (q + 1) = (b (q + 1) - b q) - γ := by
        simp [F]
        ring
      rw [hNextEq] at hNextDiff
      linarith
  · rintro ⟨hLeft, hRight⟩
    have hLeftMono : MonotoneOn F (Set.Icc 2 q) := by
      refine monotoneOn_of_le_succ Set.ordConnected_Icc ?_
      intro a _ ha hsucc
      have hSuccLeQ : a + 1 ≤ q := hsucc.2
      have hSuccSlopeLe :
          b (a + 1) - b a ≤ b q - b (q - 1) := by
        apply hSlopeMono
        · exact ⟨Nat.succ_le_succ ha.1, le_trans hSuccLeQ hqQ.le⟩
        · exact ⟨Nat.succ_le_of_lt hq, hqQ.le⟩
        · exact hSuccLeQ
      have hStep : b (a + 1) - b a ≤ γ := hSuccSlopeLe.trans hLeft
      simp [F]
      linarith
    have hRightAnti : AntitoneOn F (Set.Icc q Q) := by
      refine antitoneOn_of_succ_le Set.ordConnected_Icc ?_
      intro a _ ha hsucc
      have hSlopeLeSucc :
          b (q + 1) - b q ≤ b (a + 1) - b a := by
        apply hSlopeMono
        · exact ⟨calc
              3 ≤ q := Nat.succ_le_of_lt hq
              _ ≤ q + 1 := Nat.le_succ q,
            Nat.succ_le_of_lt hqQ⟩
        · exact ⟨calc
              3 ≤ q := Nat.succ_le_of_lt hq
              _ ≤ a := ha.1
              _ ≤ a + 1 := Nat.le_succ a,
            hsucc.2⟩
        · exact Nat.succ_le_succ ha.1
      have hStep : γ ≤ b (a + 1) - b a := hRight.trans hSlopeLeSucc
      simp [F]
      linarith
    intro r hrTwo hrQ
    by_cases hrq : r ≤ q
    · exact hLeftMono ⟨hrTwo, hrq⟩ ⟨le_of_lt hq, le_rfl⟩ hrq
    · have hqle : q ≤ r := le_of_not_ge hrq
      exact hRightAnti ⟨le_rfl, hqQ.le⟩ ⟨hqle, hrQ⟩ hqle

end Omega.Conclusion
