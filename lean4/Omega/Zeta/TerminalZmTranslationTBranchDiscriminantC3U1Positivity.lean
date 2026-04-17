import Mathlib.Tactic

namespace Omega.Zeta

/-- The quartic factor appearing in the `u = 1` discriminant slice. -/
def xiTerminalQuartic (t : ℝ) : ℝ :=
  20 * t ^ 4 - 88 * t ^ 3 + 284 * t ^ 2 + 45 * t + 22

/-- Chapter-local placeholder for the factored `D_t(1)` slice. -/
def xiTerminalDtAtOne (t : ℝ) : ℝ :=
  (t - 2) * xiTerminalQuartic t

/-- Explicit sum-of-squares decomposition of the quartic factor. -/
theorem xiTerminalQuartic_sum_of_squares (t : ℝ) :
    xiTerminalQuartic t =
      20 * (t ^ 2 - ((11 : ℝ) / 5) * t) ^ 2 +
        ((936 : ℝ) / 5) * (t + (25 : ℝ) / 208) ^ 2 + (8027 : ℝ) / 416 := by
  unfold xiTerminalQuartic
  ring

/-- The quartic factor is strictly positive on all real inputs. -/
theorem xiTerminalQuartic_pos (t : ℝ) : 0 < xiTerminalQuartic t := by
  rw [xiTerminalQuartic_sum_of_squares]
  nlinarith [sq_nonneg (t ^ 2 - ((11 : ℝ) / 5) * t), sq_nonneg (t + (25 : ℝ) / 208)]

/-- The `u = 1` slice factors through the positive quartic and the simple root `t = 2`. -/
theorem xiTerminalDtAtOne_factorization (t : ℝ) :
    xiTerminalDtAtOne t = (t - 2) * xiTerminalQuartic t := by
  rfl

/-- The positive quartic excludes every real resonance except `t = 2`. -/
theorem xiTerminalDtAtOne_eq_zero_iff (t : ℝ) :
    xiTerminalDtAtOne t = 0 ↔ t = 2 := by
  constructor
  · intro h
    rw [xiTerminalDtAtOne_factorization] at h
    have hq : 0 < xiTerminalQuartic t := xiTerminalQuartic_pos t
    nlinarith
  · intro h
    simp [xiTerminalDtAtOne, h]

/-- Paper-facing package: the quartic factor has the displayed sum-of-squares decomposition, is
strictly positive on `ℝ`, and therefore the `u = 1` discriminant slice has the unique real
resonance `t = 2`.
    thm:xi-terminal-zm-translation-t-branch-discriminant-c3-u1-positivity -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_u1_positivity :
    (∀ t : ℝ,
      xiTerminalQuartic t =
        20 * (t ^ 2 - ((11 : ℝ) / 5) * t) ^ 2 +
          ((936 : ℝ) / 5) * (t + (25 : ℝ) / 208) ^ 2 + (8027 : ℝ) / 416) ∧
    (∀ t : ℝ, 0 < xiTerminalQuartic t) ∧
    (∀ t : ℝ, xiTerminalDtAtOne t = 0 → t = 2) := by
  exact ⟨xiTerminalQuartic_sum_of_squares, xiTerminalQuartic_pos,
    fun t => (xiTerminalDtAtOne_eq_zero_iff t).1⟩

end Omega.Zeta
