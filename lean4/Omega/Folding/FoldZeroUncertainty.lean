import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega

/-- The centered `L²` gap for a two-fiber fold law. -/
noncomputable def foldZeroL2Gap (u v : ℝ) : ℝ :=
  (u - 1 / 2) ^ 2 + (v - 1 / 2) ^ 2

/-- The collision-gap quantity entering the Parseval bound. -/
noncomputable def foldZeroCollisionGap (u v : ℝ) : ℝ :=
  1 + foldZeroL2Gap u v

/-- The max-fiber gap is controlled by the centered `L²` gap. -/
noncomputable def foldZeroMaxFiberGapBound (u v : ℝ) : Prop :=
  max u v - 1 / 2 ≤ Real.sqrt (foldZeroL2Gap u v)

/-- The Shannon/KL gap used in the paper package. -/
def foldZeroKLGapBound (H H2 : ℝ) : Prop :=
  H2 ≤ H

/-- Fourier peak bound obtained from Parseval and the collision gap. -/
noncomputable def foldZeroFourierPeakBound (ξ u v : ℝ) : Prop :=
  ξ ^ 2 ≤ foldZeroCollisionGap u v

/-- Zero-uncertainty package for a two-fiber fold law: the centered `L²` identity, the `L∞ ≤ L²`
max-fiber control, the entropy-gap monotonicity `H ≥ H₂`, and the Fourier peak bound deduced from
the collision gap.
    thm:fold-zero-uncertainty -/
theorem paper_fold_zero_uncertainty
    (u v H H2 ξ collision : ℝ)
    (hsum : u + v = 1)
    (hentropy : H2 ≤ H)
    (hparseval : ξ ^ 2 ≤ collision)
    (hcollision : collision = foldZeroCollisionGap u v) :
    foldZeroL2Gap u v = u ^ 2 + v ^ 2 - 1 / 2 ∧
      foldZeroMaxFiberGapBound u v ∧
      foldZeroKLGapBound H H2 ∧
      foldZeroFourierPeakBound ξ u v := by
  have hL2 :
      foldZeroL2Gap u v = u ^ 2 + v ^ 2 - 1 / 2 := by
    unfold foldZeroL2Gap
    nlinarith [hsum]
  have hgap_nonneg : 0 ≤ foldZeroL2Gap u v := by
    unfold foldZeroL2Gap
    positivity
  have hmax_ge_half : 1 / 2 ≤ max u v := by
    have hu_max : u ≤ max u v := le_max_left _ _
    have hv_max : v ≤ max u v := le_max_right _ _
    nlinarith [hsum, hu_max, hv_max]
  have hmax_gap_nonneg : 0 ≤ max u v - 1 / 2 := by
    nlinarith
  have hsq :
      (max u v - 1 / 2) ^ 2 ≤ foldZeroL2Gap u v := by
    by_cases huv : u ≤ v
    · have hmax : max u v = v := max_eq_right huv
      unfold foldZeroL2Gap
      rw [hmax]
      nlinarith [sq_nonneg (u - 1 / 2 : ℝ)]
    · have hvu : v ≤ u := le_of_not_ge huv
      have hmax : max u v = u := max_eq_left hvu
      unfold foldZeroL2Gap
      rw [hmax]
      nlinarith [sq_nonneg (v - 1 / 2 : ℝ)]
  have hmaxGap : foldZeroMaxFiberGapBound u v := by
    unfold foldZeroMaxFiberGapBound
    have hsqrt : (Real.sqrt (foldZeroL2Gap u v)) ^ 2 = foldZeroL2Gap u v := by
      rw [Real.sq_sqrt hgap_nonneg]
    nlinarith [hsq, hsqrt, hmax_gap_nonneg, Real.sqrt_nonneg (foldZeroL2Gap u v)]
  have hpeak : foldZeroFourierPeakBound ξ u v := by
    unfold foldZeroFourierPeakBound foldZeroCollisionGap
    calc
      ξ ^ 2 ≤ collision := hparseval
      _ = 1 + foldZeroL2Gap u v := by simpa [foldZeroCollisionGap] using hcollision
  exact ⟨hL2, hmaxGap, hentropy, hpeak⟩

end Omega
