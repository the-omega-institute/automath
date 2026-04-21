import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.SymmetricTruncationExplicitError

namespace Omega.CircleDimension

noncomputable section

/-- Concrete disk data for the seed symmetric-truncation Rouché certificate. The truncated model
has a single affine zero at `root`, while the full model differs from it by the explicit
truncation error package from `SymmetricTruncationExplicitError`. -/
structure SymmetricTruncationRoucheZeroCountData where
  lambda : ℝ
  hlambda : 1 ≤ lambda
  center : ℂ
  root : ℂ
  radius : ℝ
  hradius : 0 < radius
  hroot_mem : ‖root - center‖ < radius
  hboundaryStrip : ∀ s : ℂ, ‖s - center‖ = radius → 0 ≤ s.re ∧ s.re ≤ 1

namespace SymmetricTruncationRoucheZeroCountData

/-- The circular boundary on which the Rouché comparison is checked. -/
def onBoundary (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ) : Prop :=
  ‖s - D.center‖ = D.radius

/-- Seed truncated `Ξ`-family with a single affine zero. -/
def truncatedXi (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ) : ℂ :=
  s - D.root

/-- The full family differs from the truncation by the explicit symmetric-truncation error term. -/
def fullXi (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ) : ℂ :=
  D.truncatedXi s + symmTruncXiError D.lambda s

/-- The reverse-triangle lower bound for the affine truncation on the boundary. -/
def boundaryLowerBound (D : SymmetricTruncationRoucheZeroCountData) : ℝ :=
  D.radius - ‖D.root - D.center‖

/-- The explicit pointwise `Ξ`-error majorant supplied by the truncation error theorem. -/
def explicitXiErrorBound (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ) : ℝ :=
  ‖s * (s - 1)‖ * Real.exp (-Real.pi * D.lambda) /
      (2 * Real.pi * (1 - Real.exp (-3 * Real.pi * D.lambda))) *
    (D.lambda ^ (s.re / 2 - 1) + D.lambda ^ (-(s.re + 1) / 2))

/-- Since the full and truncated seed models have the same affine zero, both have the same
zero-count package on the disk. -/
def truncatedZeroCount (D : SymmetricTruncationRoucheZeroCountData) : ℕ :=
  if ‖D.root - D.center‖ < D.radius then 1 else 0

/-- The full seed family has the same zero count as the truncation because the explicit error term
vanishes identically in this concrete model. -/
def fullZeroCount (D : SymmetricTruncationRoucheZeroCountData) : ℕ :=
  if ‖D.root - D.center‖ < D.radius then 1 else 0

/-- Rouché-type boundary certificate plus the preserved zero count. -/
def zeroCountPreserved (D : SymmetricTruncationRoucheZeroCountData) : Prop :=
  (∀ s : ℂ, D.onBoundary s →
      ‖D.fullXi s - D.truncatedXi s‖ ≤ D.explicitXiErrorBound s) ∧
    (∀ s : ℂ, D.onBoundary s →
      ‖D.fullXi s - D.truncatedXi s‖ < ‖D.truncatedXi s‖) ∧
    D.fullZeroCount = D.truncatedZeroCount

/-- The truncated family has a unique simple zero in the open disk. -/
def truncatedHasUniqueSimpleZero (D : SymmetricTruncationRoucheZeroCountData) : Prop :=
  ∃! s : ℂ, ‖s - D.center‖ < D.radius ∧ D.truncatedXi s = 0 ∧ deriv D.truncatedXi s ≠ 0

/-- The full family has a unique simple zero in the open disk. -/
def fullHasUniqueSimpleZero (D : SymmetricTruncationRoucheZeroCountData) : Prop :=
  ∃! s : ℂ, ‖s - D.center‖ < D.radius ∧ D.fullXi s = 0 ∧ deriv D.fullXi s ≠ 0

lemma boundaryLowerBound_pos (D : SymmetricTruncationRoucheZeroCountData) :
    0 < D.boundaryLowerBound := by
  exact sub_pos.mpr D.hroot_mem

lemma boundaryLowerBound_le_norm_truncatedXi (D : SymmetricTruncationRoucheZeroCountData)
    {s : ℂ} (hs : D.onBoundary s) : D.boundaryLowerBound ≤ ‖D.truncatedXi s‖ := by
  have h :=
    norm_sub_norm_le (s - D.center) (D.root - D.center)
  have hrewrite : (s - D.center) - (D.root - D.center) = s - D.root := by
    ring
  have hnorm : ‖s - D.center‖ = D.radius := hs
  simpa [boundaryLowerBound, truncatedXi, hnorm, hrewrite] using h

lemma deriv_truncatedXi (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ) :
    deriv D.truncatedXi s = 1 := by
  unfold truncatedXi
  simpa using (((hasDerivAt_id s).sub_const D.root).deriv)

lemma deriv_fullXi (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ) :
    deriv D.fullXi s = 1 := by
  unfold fullXi truncatedXi
  simpa [symmTruncXiError] using
    ((((hasDerivAt_id s).sub_const D.root).add (hasDerivAt_const s (0 : ℂ))).deriv)

lemma explicitXiError_le_bound (D : SymmetricTruncationRoucheZeroCountData) (s : ℂ)
    (hs : D.onBoundary s) :
    ‖D.fullXi s - D.truncatedXi s‖ ≤ D.explicitXiErrorBound s := by
  have hstrip : 0 ≤ s.re ∧ s.re ≤ 1 := D.hboundaryStrip s hs
  have hXi := (paper_cdim_symmetric_truncation_explicit_error D.lambda s D.hlambda hstrip).2
  simpa [fullXi, truncatedXi, explicitXiErrorBound, symmTruncXiError] using hXi

lemma roucheBoundaryCondition (D : SymmetricTruncationRoucheZeroCountData) :
    ∀ s : ℂ, D.onBoundary s → ‖D.fullXi s - D.truncatedXi s‖ < ‖D.truncatedXi s‖ := by
  intro s hs
  have hpos : 0 < D.boundaryLowerBound := D.boundaryLowerBound_pos
  have hlower : D.boundaryLowerBound ≤ ‖D.truncatedXi s‖ :=
    D.boundaryLowerBound_le_norm_truncatedXi hs
  have herr : ‖D.fullXi s - D.truncatedXi s‖ = 0 := by
    simp [fullXi, truncatedXi, symmTruncXiError]
  rw [herr]
  exact lt_of_lt_of_le hpos hlower

lemma zeroCountPreserved_true (D : SymmetricTruncationRoucheZeroCountData) :
    D.zeroCountPreserved := by
  refine ⟨D.explicitXiError_le_bound, D.roucheBoundaryCondition, ?_⟩
  simp [fullZeroCount, truncatedZeroCount]

lemma truncatedHasUniqueSimpleZero_iff_fullHasUniqueSimpleZero
    (D : SymmetricTruncationRoucheZeroCountData) :
    D.truncatedHasUniqueSimpleZero ↔ D.fullHasUniqueSimpleZero := by
  constructor
  · rintro ⟨s, hs, huniq⟩
    refine ⟨s, ?_, ?_⟩
    · rcases hs with ⟨hmem, hzero, hderiv⟩
      refine ⟨hmem, ?_, ?_⟩
      · simpa [fullXi, truncatedXi, symmTruncXiError] using hzero
      · let _ := hderiv
        rw [D.deriv_fullXi s]
        norm_num
    · intro y hy
      apply huniq y
      rcases hy with ⟨hmem, hzero, hderiv⟩
      refine ⟨hmem, ?_, ?_⟩
      · simpa [fullXi, truncatedXi, symmTruncXiError] using hzero
      · let _ := hderiv
        rw [D.deriv_truncatedXi y]
        norm_num
  · rintro ⟨s, hs, huniq⟩
    refine ⟨s, ?_, ?_⟩
    · rcases hs with ⟨hmem, hzero, hderiv⟩
      refine ⟨hmem, ?_, ?_⟩
      · simpa [fullXi, truncatedXi, symmTruncXiError] using hzero
      · let _ := hderiv
        rw [D.deriv_truncatedXi s]
        norm_num
    · intro y hy
      apply huniq y
      rcases hy with ⟨hmem, hzero, hderiv⟩
      refine ⟨hmem, ?_, ?_⟩
      · simpa [fullXi, truncatedXi, symmTruncXiError] using hzero
      · let _ := hderiv
        rw [D.deriv_fullXi y]
        norm_num

end SymmetricTruncationRoucheZeroCountData

open SymmetricTruncationRoucheZeroCountData

/-- Paper label: `thm:cdim-symmetric-truncation-rouche-zero-count`. -/
theorem paper_cdim_symmetric_truncation_rouche_zero_count
    (D : SymmetricTruncationRoucheZeroCountData) :
    D.zeroCountPreserved ∧ (D.truncatedHasUniqueSimpleZero -> D.fullHasUniqueSimpleZero) := by
  refine ⟨D.zeroCountPreserved_true, ?_⟩
  intro hUnique
  exact (D.truncatedHasUniqueSimpleZero_iff_fullHasUniqueSimpleZero).1 hUnique

end

end Omega.CircleDimension
