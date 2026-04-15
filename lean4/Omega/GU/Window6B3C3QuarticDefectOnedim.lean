import Mathlib.Tactic
import Omega.GU.Window6B3C3TriaxialSelectionIdealFactorization

namespace Omega.GU

open Finset
open scoped BigOperators

/-- The quartic coordinate sum on `ℝ³`. -/
def quarticSigma4 (u : ℝ × ℝ × ℝ) : ℝ :=
  u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4

/-- The axis directions on the unit sphere, recorded through squared coordinates. -/
def axisSqDirections (u : ℝ × ℝ × ℝ) : Prop :=
  (u.1 ^ 2 = 1 ∧ u.2.1 = 0 ∧ u.2.2 = 0) ∨
    (u.1 = 0 ∧ u.2.1 ^ 2 = 1 ∧ u.2.2 = 0) ∨
    (u.1 = 0 ∧ u.2.1 = 0 ∧ u.2.2 ^ 2 = 1)

/-- The body-diagonal directions on the unit sphere, recorded through squared coordinates. -/
def bodyDiagonalSqDirections (u : ℝ × ℝ × ℝ) : Prop :=
  u.1 ^ 2 = 1 / 3 ∧ u.2.1 ^ 2 = 1 / 3 ∧ u.2.2 ^ 2 = 1 / 3

private lemma quarticSigma4_bounds (u : ℝ × ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = 1) :
    (1 / 3 : ℝ) ≤ quarticSigma4 u ∧ quarticSigma4 u ≤ 1 := by
  constructor
  · dsimp [quarticSigma4] at *
    nlinarith [sq_nonneg (u.1 ^ 2 - u.2.1 ^ 2), sq_nonneg (u.1 ^ 2 - u.2.2 ^ 2),
      sq_nonneg (u.2.1 ^ 2 - u.2.2 ^ 2)]
  · dsimp [quarticSigma4] at *
    nlinarith [mul_nonneg (sq_nonneg u.1) (sq_nonneg u.2.1),
      mul_nonneg (sq_nonneg u.1) (sq_nonneg u.2.2),
      mul_nonneg (sq_nonneg u.2.1) (sq_nonneg u.2.2)]

private lemma quarticSigma4_eq_one_iff (u : ℝ × ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = 1) :
    quarticSigma4 u = 1 ↔ axisSqDirections u := by
  let a : ℝ := u.1 ^ 2
  let b : ℝ := u.2.1 ^ 2
  let c : ℝ := u.2.2 ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  constructor
  · intro hs
    have hcross : a * b + a * c + b * c = 0 := by
      dsimp [quarticSigma4, a, b, c] at hs hu ⊢
      nlinarith
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
    have hac_nonneg : 0 ≤ a * c := mul_nonneg ha hc
    have hbc_nonneg : 0 ≤ b * c := mul_nonneg hb hc
    have hab : a * b = 0 := by
      have hle : a * b ≤ 0 := by nlinarith
      exact le_antisymm hle hab_nonneg
    have hac : a * c = 0 := by
      have hle : a * c ≤ 0 := by nlinarith
      exact le_antisymm hle hac_nonneg
    have hbc : b * c = 0 := by
      have hle : b * c ≤ 0 := by nlinarith
      exact le_antisymm hle hbc_nonneg
    have hpos : 0 < a ∨ 0 < b ∨ 0 < c := by
      by_contra hneg
      push_neg at hneg
      nlinarith [hu, ha, hb, hc]
    rcases hpos with ha_pos | hb_pos | hc_pos
    · have hb0 : b = 0 := by
        exact (mul_eq_zero.mp hab).resolve_left (ne_of_gt ha_pos)
      have hc0 : c = 0 := by
        exact (mul_eq_zero.mp hac).resolve_left (ne_of_gt ha_pos)
      left
      constructor
      · dsimp [a] at *
        nlinarith [hu, hb0, hc0]
      constructor
      · exact sq_eq_zero_iff.mp (by simpa [b] using hb0)
      · exact sq_eq_zero_iff.mp (by simpa [c] using hc0)
    · have ha0 : a = 0 := by
        exact (mul_eq_zero.mp hab).resolve_right (ne_of_gt hb_pos)
      have hc0 : c = 0 := by
        exact (mul_eq_zero.mp hbc).resolve_left (ne_of_gt hb_pos)
      right
      left
      constructor
      · exact sq_eq_zero_iff.mp (by simpa [a] using ha0)
      constructor
      · dsimp [b] at *
        nlinarith [hu, ha0, hc0]
      · exact sq_eq_zero_iff.mp (by simpa [c] using hc0)
    · have ha0 : a = 0 := by
        exact (mul_eq_zero.mp hac).resolve_right (ne_of_gt hc_pos)
      have hb0 : b = 0 := by
        exact (mul_eq_zero.mp hbc).resolve_right (ne_of_gt hc_pos)
      right
      right
      constructor
      · exact sq_eq_zero_iff.mp (by simpa [a] using ha0)
      constructor
      · exact sq_eq_zero_iff.mp (by simpa [b] using hb0)
      · dsimp [c] at *
        nlinarith [hu, ha0, hb0]
  · intro hAxis
    rcases hAxis with hAxis | hAxis | hAxis
    · rcases hAxis with ⟨hx, hy, hz⟩
      dsimp [quarticSigma4]
      nlinarith [hx]
    · rcases hAxis with ⟨hx, hy, hz⟩
      dsimp [quarticSigma4]
      nlinarith [hy]
    · rcases hAxis with ⟨hx, hy, hz⟩
      dsimp [quarticSigma4]
      nlinarith [hz]

private lemma quarticSigma4_eq_third_iff (u : ℝ × ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = 1) :
    quarticSigma4 u = 1 / 3 ↔ bodyDiagonalSqDirections u := by
  let a : ℝ := u.1 ^ 2
  let b : ℝ := u.2.1 ^ 2
  let c : ℝ := u.2.2 ^ 2
  have habsq : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have hacsq : 0 ≤ (a - c) ^ 2 := sq_nonneg (a - c)
  have hbcsq : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  constructor
  · intro hs
    have hsumsq : (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 = 0 := by
      dsimp [quarticSigma4, a, b, c] at hs hu ⊢
      nlinarith
    have hab0 : (a - b) ^ 2 = 0 := by
      have hle : (a - b) ^ 2 ≤ 0 := by nlinarith
      exact le_antisymm hle habsq
    have hac0 : (a - c) ^ 2 = 0 := by
      have hle : (a - c) ^ 2 ≤ 0 := by nlinarith
      exact le_antisymm hle hacsq
    have hab : a = b := by nlinarith
    have hac : a = c := by nlinarith
    have hu' : a + b + c = 1 := by
      simpa [a, b, c] using hu
    have ha : a = 1 / 3 := by
      nlinarith [hu', hab, hac]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [a] at ha
      simpa using ha
    · dsimp [b] at hab
      nlinarith [ha, hab]
    · dsimp [c] at hac
      nlinarith [ha, hac]
  · rintro ⟨hx, hy, hz⟩
    dsimp [quarticSigma4]
    nlinarith [hx, hy, hz]

set_option maxHeartbeats 400000 in
/-- Explicit quadratic and quartic moment identities on the `window-6` visible `B₃/C₃`
supports.
    thm:window6-b3c3-quartic-defect-onedim -/
theorem paper_window6_b3c3_quartic_defect_onedim (u : ℝ × ℝ × ℝ) :
    let s2 : ℝ := u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2
    let s4 : ℝ := u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4
    let h4 : ℝ := s4 - (3 / 5 : ℝ) * s2 ^ 2
    (Finset.sum b3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 2) =
        10 * s2) ∧
      (Finset.sum c3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 2) =
        16 * s2) ∧
      (Finset.sum b3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
        (54 / 5 : ℝ) * s2 ^ 2 - 2 * h4) ∧
      (Finset.sum c3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
        (144 / 5 : ℝ) * s2 ^ 2 + 28 * h4) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [b3VisibleSupport, zeroWeight, phiB2_12, phiB2_13, phiB2_23]
    ring
  · simp [c3VisibleSupport, zeroWeight, phiC2_12, phiC2_13, phiC2_23]
    ring
  · simp [b3VisibleSupport, zeroWeight, phiB2_12, phiB2_13, phiB2_23]
    ring
  · simp [c3VisibleSupport, zeroWeight, phiC2_12, phiC2_13, phiC2_23]
    ring

set_option maxHeartbeats 400000 in
/-- On the unit sphere, the visible `B₃` and `C₃` quartic moments reduce to affine functions of
    `Σ uᵢ⁴`, so their extrema occur on axes and body diagonals with reversed roles.
    thm:window6-b3c3-quartic-axis-diagonal-reversal -/
theorem paper_window6_b3c3_quartic_axis_diagonal_reversal
    (u : ℝ × ℝ × ℝ)
    (hu : u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = 1) :
    let σ4 : ℝ := quarticSigma4 u
    let m4B : ℝ :=
      Finset.sum b3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4)
    let m4C : ℝ :=
      Finset.sum c3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4)
    (m4B = 12 - 2 * σ4) ∧
      (m4C = 12 + 28 * σ4) ∧
      ((1 / 3 : ℝ) ≤ σ4 ∧ σ4 ≤ 1) ∧
      ((10 ≤ m4B ∧ m4B ≤ 34 / 3) ∧ (64 / 3 ≤ m4C ∧ m4C ≤ 40)) ∧
      ((m4B = 10 ↔ axisSqDirections u) ∧
        (m4B = 34 / 3 ↔ bodyDiagonalSqDirections u) ∧
        (m4C = 40 ↔ axisSqDirections u) ∧
        (m4C = 64 / 3 ↔ bodyDiagonalSqDirections u)) := by
  dsimp
  have hpack := paper_window6_b3c3_quartic_defect_onedim u
  rcases hpack with ⟨_, _, hBraw, hCraw⟩
  have hB : Finset.sum b3VisibleSupport
      (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
      12 - 2 * quarticSigma4 u := by
    calc
      Finset.sum b3VisibleSupport
          (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
          (54 / 5 : ℝ) * (u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2) ^ 2 -
            2 * (quarticSigma4 u - (3 / 5 : ℝ) * (u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2) ^ 2) := by
        simpa [quarticSigma4] using hBraw
      _ = 12 - 2 * quarticSigma4 u := by nlinarith [hu]
  have hC : Finset.sum c3VisibleSupport
      (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
      12 + 28 * quarticSigma4 u := by
    calc
      Finset.sum c3VisibleSupport
          (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
          (144 / 5 : ℝ) * (u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2) ^ 2 +
            28 * (quarticSigma4 u - (3 / 5 : ℝ) * (u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2) ^ 2) := by
        simpa [quarticSigma4] using hCraw
      _ = 12 + 28 * quarticSigma4 u := by nlinarith [hu]
  have hBounds := quarticSigma4_bounds u hu
  have hAxis : quarticSigma4 u = 1 ↔ axisSqDirections u := quarticSigma4_eq_one_iff u hu
  have hDiag : quarticSigma4 u = 1 / 3 ↔ bodyDiagonalSqDirections u := quarticSigma4_eq_third_iff u hu
  refine ⟨hB, hC, hBounds, ?_, ?_⟩
  · constructor
    · constructor <;> linarith [hB, hBounds.1, hBounds.2]
    · constructor <;> linarith [hC, hBounds.1, hBounds.2]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro hm
        apply hAxis.mp
        linarith [hB, hm]
      · intro hAxis'
        have hσ : quarticSigma4 u = 1 := hAxis.mpr hAxis'
        linarith [hB, hσ]
    · constructor
      · intro hm
        apply hDiag.mp
        linarith [hB, hm]
      · intro hDiag'
        have hσ : quarticSigma4 u = 1 / 3 := hDiag.mpr hDiag'
        linarith [hB, hσ]
    · constructor
      · intro hm
        apply hAxis.mp
        linarith [hC, hm]
      · intro hAxis'
        have hσ : quarticSigma4 u = 1 := hAxis.mpr hAxis'
        linarith [hC, hσ]
    · constructor
      · intro hm
        apply hDiag.mp
        linarith [hC, hm]
      · intro hDiag'
        have hσ : quarticSigma4 u = 1 / 3 := hDiag.mpr hDiag'
        linarith [hC, hσ]

end Omega.GU
