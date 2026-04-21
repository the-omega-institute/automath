import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Omega.Folding.HaltingLeyangHolographicEncoding

namespace Omega.Folding

open Complex

noncomputable section

/-- Dyadic weight `2^{-e}` appearing in the halting-gap estimates. -/
def dyadicScale (e : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ e

/-- The power test function used to read the `q`th moment on the unit circle. -/
def unitCirclePowerTest (q : ℕ) (z : UnitCirclePoint) : ℂ :=
  z.1 ^ q

/-- Threshold used to separate the halting and non-halting moment regimes. -/
def haltingW1Threshold (e : ℕ) : ℝ :=
  dyadicScale e / 6

/-- The moment error produced from a `W₁` approximation via a `q`-Lipschitz test function. -/
def powerMomentErrorBound (q : ℕ) (w1 : ℝ) : ℝ :=
  q * w1

lemma dyadicScale_pos (e : ℕ) : 0 < dyadicScale e := by
  unfold dyadicScale
  positivity

lemma dyadicScale_succ (e : ℕ) : dyadicScale (e + 1) = dyadicScale e / 2 := by
  unfold dyadicScale
  rw [pow_succ, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- On the unit circle the power test `z ↦ z^q` is `q`-Lipschitz for the ambient Euclidean norm. -/
theorem unitCirclePowerTest_lipschitz (q : ℕ) (z w : UnitCirclePoint) :
    ‖unitCirclePowerTest q z - unitCirclePowerTest q w‖ ≤ q * ‖z.1 - w.1‖ := by
  have hgeom :=
    (Commute.all z.1 w.1).mul_geom_sum₂ q
  have hfactor :
      z.1 ^ q - w.1 ^ q =
        (z.1 - w.1) * ∑ i ∈ Finset.range q, z.1 ^ i * w.1 ^ (q - 1 - i) := by
    simpa [unitCirclePowerTest] using hgeom.symm
  simp [unitCirclePowerTest]
  rw [hfactor]
  calc
    ‖(z.1 - w.1) * ∑ i ∈ Finset.range q, z.1 ^ i * w.1 ^ (q - 1 - i)‖
        = ‖z.1 - w.1‖ * ‖∑ i ∈ Finset.range q, z.1 ^ i * w.1 ^ (q - 1 - i)‖ := by
            rw [norm_mul]
    _ ≤ ‖z.1 - w.1‖ * ∑ i ∈ Finset.range q, ‖z.1 ^ i * w.1 ^ (q - 1 - i)‖ := by
          gcongr
          exact norm_sum_le _ _
    _ = ‖z.1 - w.1‖ * q := by
          simp [z.property, w.property]
    _ = q * ‖z.1 - w.1‖ := by
          ring

/-- Converting the `W₁` control `w1 ≤ 2^{-e} / (12 q)` into the corresponding moment error bound
`≤ 2^{-e} / 12`. -/
theorem powerMomentError_of_w1
    {e q : ℕ} (hq : 0 < q) {momentError w1 : ℝ}
    (hMoment : momentError ≤ powerMomentErrorBound q w1)
    (hW1 : w1 ≤ dyadicScale e / (12 * q)) :
    momentError ≤ dyadicScale e / 12 := by
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hw1' : (q : ℝ) * w1 ≤ dyadicScale e / 12 := by
    have := mul_le_mul_of_nonneg_left hW1 (show (0 : ℝ) ≤ q by positivity)
    have hrewrite : (q : ℝ) * (dyadicScale e / (12 * q)) = dyadicScale e / 12 := by
      field_simp [hqne]
    simpa [hrewrite, powerMomentErrorBound] using this
  simpa [powerMomentErrorBound] using hMoment.trans hw1'

/-- Paper label: `thm:fold-computability-halting-no-uniform-w1-learning`.
The theorem packages the threshold argument: a `W₁` approximation whose power-moment error is
controlled at scale `2^{-e} / (12 q)` already separates the zero case from the halting gap
`≥ 2^{-e-1}`. -/
theorem paper_fold_computability_halting_no_uniform_w1_learning
    (e q : ℕ) (hq : 0 < q) (approxMoment targetMoment w1 : ℝ)
    (hMoment : |approxMoment - targetMoment| ≤ powerMomentErrorBound q w1)
    (hW1 : w1 ≤ dyadicScale e / (12 * q))
    (hGap : targetMoment = 0 ∨ dyadicScale (e + 1) ≤ targetMoment) :
    haltingW1Threshold e ≤ approxMoment ↔ dyadicScale (e + 1) ≤ targetMoment := by
  have hsmall : |approxMoment - targetMoment| ≤ dyadicScale e / 12 :=
    powerMomentError_of_w1 hq hMoment hW1
  constructor
  · intro hthr
    rcases hGap with hzero | hlarge
    · exfalso
      have habs : |approxMoment| ≤ dyadicScale e / 12 := by
        simpa [hzero, sub_zero] using hsmall
      have happrox_le : approxMoment ≤ dyadicScale e / 12 := by
        exact (le_abs_self approxMoment).trans habs
      have : dyadicScale e / 6 ≤ dyadicScale e / 12 := le_trans hthr happrox_le
      have hpos : 0 < dyadicScale e := dyadicScale_pos e
      linarith
    · exact hlarge
  · intro hlarge
    have hinterval := abs_sub_le_iff.mp hsmall
    have happrox_ge : targetMoment - dyadicScale e / 12 ≤ approxMoment := by
      linarith
    rw [dyadicScale_succ] at hlarge
    unfold haltingW1Threshold
    have hpos : 0 < dyadicScale e := dyadicScale_pos e
    linarith

end

end Omega.Folding
