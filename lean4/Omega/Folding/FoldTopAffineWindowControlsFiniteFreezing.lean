import Mathlib.Tactic

namespace Omega.Folding

/-- The audited window-`6` top-window continuous capacity curve. -/
noncomputable def foldTopAffineWindowCapacitySix (T : ℝ) : ℝ :=
  (64 : ℝ) - 9 * (4 - T)

/-- The audited window-`6` power sum attached to the histogram `2:8, 3:4, 4:9`. -/
def foldTopAffineWindowPowerSumSix (a : ℕ) : ℕ :=
  8 * 2 ^ a + 4 * 3 ^ a + 9 * 4 ^ a

/-- The missing escort mass outside the maximal `d = 4` layer in the audited window-`6` model. -/
noncomputable def foldTopAffineWindowEscortTvSix (a : ℕ) : ℚ :=
  1 - (((9 * 4 ^ a : ℕ) : ℚ) / foldTopAffineWindowPowerSumSix a)

/-- Concrete audited window-`6` freezing package: on the top affine window `[3,4]` the continuous
capacity is exactly linear, the power sum is squeezed between the dominant `d = 4` term and the
same term plus the off-top `12` fibers at level `3`, and the escort total-variation defect is
bounded by the resulting geometric ratio. -/
def FoldTopAffineWindowControlsFiniteFreezingSpec (m : ℕ) : Prop :=
  m = 6 →
    (∀ {T : ℝ}, 3 ≤ T → T ≤ 4 →
      8 * min (2 : ℝ) T + 4 * min (3 : ℝ) T + 9 * min (4 : ℝ) T =
        foldTopAffineWindowCapacitySix T) ∧
    (∀ a : ℕ,
      9 * 4 ^ a ≤ foldTopAffineWindowPowerSumSix a ∧
        foldTopAffineWindowPowerSumSix a ≤ 9 * 4 ^ a + 12 * 3 ^ a ∧
        foldTopAffineWindowEscortTvSix a ≤ (((12 * 3 ^ a : ℕ) : ℚ) / (9 * 4 ^ a)))

private theorem foldTopAffineWindowEscortTvSix_bound (a : ℕ) :
    foldTopAffineWindowEscortTvSix a ≤ (((12 * 3 ^ a : ℕ) : ℚ) / (9 * 4 ^ a)) := by
  have hmain : 9 * 4 ^ a ≤ foldTopAffineWindowPowerSumSix a := by
    unfold foldTopAffineWindowPowerSumSix
    omega
  have hnumNat : foldTopAffineWindowPowerSumSix a - 9 * 4 ^ a ≤ 12 * 3 ^ a := by
    unfold foldTopAffineWindowPowerSumSix
    have h23 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by omega : 2 ≤ 3) a
    omega
  have hmain_pos_nat : 0 < 9 * 4 ^ a := by
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hmain_pos : (0 : ℚ) < 9 * 4 ^ a := by
    exact_mod_cast hmain_pos_nat
  have hsum_pos : (0 : ℚ) < foldTopAffineWindowPowerSumSix a := by
    exact_mod_cast (lt_of_lt_of_le hmain_pos_nat hmain)
  have hmain_rat : ((9 * 4 ^ a : ℕ) : ℚ) ≤ foldTopAffineWindowPowerSumSix a := by
    exact_mod_cast hmain
  let offQ : ℚ := ((12 * 3 ^ a : ℕ) : ℚ)
  have hnum_rat : (((foldTopAffineWindowPowerSumSix a - 9 * 4 ^ a : ℕ) : ℚ)) ≤ offQ := by
    dsimp [offQ]
    exact_mod_cast hnumNat
  have hrewrite :
      foldTopAffineWindowEscortTvSix a =
        (((foldTopAffineWindowPowerSumSix a - 9 * 4 ^ a : ℕ) : ℚ) / foldTopAffineWindowPowerSumSix a) := by
    unfold foldTopAffineWindowEscortTvSix
    have hcast :
        (((foldTopAffineWindowPowerSumSix a - 9 * 4 ^ a : ℕ) : ℚ)) =
          (foldTopAffineWindowPowerSumSix a : ℚ) - ((9 * 4 ^ a : ℕ) : ℚ) := by
      rw [Nat.cast_sub hmain]
    rw [hcast]
    field_simp [ne_of_gt hsum_pos]
  rw [hrewrite]
  refine (div_le_div_iff₀ hsum_pos hmain_pos).2 ?_
  have hmain_nonneg : (0 : ℚ) ≤ ((9 * 4 ^ a : ℕ) : ℚ) := by positivity
  have hmul₁ :
      (((9 * 4 ^ a : ℕ) : ℚ)) * (((foldTopAffineWindowPowerSumSix a - 9 * 4 ^ a : ℕ) : ℚ)) ≤
        (((9 * 4 ^ a : ℕ) : ℚ)) * offQ := by
    exact mul_le_mul_of_nonneg_left hnum_rat hmain_nonneg
  have hscale_nonneg : (0 : ℚ) ≤ offQ := by
    dsimp [offQ]
    positivity
  have hmul₂ : (((9 * 4 ^ a : ℕ) : ℚ)) * offQ ≤
      offQ * foldTopAffineWindowPowerSumSix a := by
    calc
      (((9 * 4 ^ a : ℕ) : ℚ)) * offQ ≤
          (foldTopAffineWindowPowerSumSix a : ℚ) * offQ := by
            exact mul_le_mul_of_nonneg_right hmain_rat hscale_nonneg
      _ = offQ * foldTopAffineWindowPowerSumSix a := by ring
  exact le_trans (by simpa [mul_comm] using hmul₁) hmul₂

/-- Paper label: `thm:fold-top-affine-window-controls-finite-freezing`. -/
theorem paper_fold_top_affine_window_controls_finite_freezing (m : ℕ) :
    FoldTopAffineWindowControlsFiniteFreezingSpec m := by
  intro hm
  subst hm
  refine ⟨?_, ?_⟩
  · intro T h3 h4
    rw [foldTopAffineWindowCapacitySix]
    rw [min_eq_left (by linarith), min_eq_left (by linarith), min_eq_right h4]
    ring
  · intro a
    refine ⟨by
      unfold foldTopAffineWindowPowerSumSix
      omega, ?_, foldTopAffineWindowEscortTvSix_bound a⟩
    unfold foldTopAffineWindowPowerSumSix
    have h23 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by omega : 2 ≤ 3) a
    omega

end Omega.Folding
