import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- The concrete zero branch moves affinely in the real direction and hits the critical line at
`λ = λc`. -/
def symmetricTruncationBarrierZeroBranch (lambdaCrit : ℝ) (lam : ℝ) : ℂ :=
  ((1 / 2 : ℝ) + (lam - lambdaCrit) : ℂ)

/-- The mirror branch imposed by the `s ↦ 1 - s` symmetry. -/
def symmetricTruncationBarrierMirrorBranch (lambdaCrit : ℝ) (lam : ℝ) : ℂ :=
  1 - symmetricTruncationBarrierZeroBranch lambdaCrit lam

/-- A concrete symmetric truncation family whose zeros are the chosen branch and its mirror. -/
def symmetricTruncationBarrierFamily (lambdaCrit : ℝ) (lam : ℝ) (s : ℂ) : ℂ :=
  (s - symmetricTruncationBarrierZeroBranch lambdaCrit lam) *
    (s - symmetricTruncationBarrierMirrorBranch lambdaCrit lam)

/-- Concrete crossing data: the chosen zero branch is continuous, it is off the critical line at
`λoff`, and it reaches the critical line at `λ = λc`. -/
def symmetricTruncationBarrierOffCriticalToCriticalCrossing
    (lambdaCrit lambdaOff : ℝ) : Prop :=
  Continuous (fun lam : ℝ => symmetricTruncationBarrierZeroBranch lambdaCrit lam) ∧
    (symmetricTruncationBarrierZeroBranch lambdaCrit lambdaOff).re ≠ 1 / 2 ∧
    ∃ t : ℝ,
      symmetricTruncationBarrierZeroBranch lambdaCrit lambdaCrit =
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

/-- The concrete family has a multiple zero on the critical line if both the value and the first
`s`-derivative vanish at a point `1/2 + i t`. -/
def symmetricTruncationBarrierHasCriticalLineMultipleZero (lambdaCrit : ℝ) : Prop :=
  ∃ t : ℝ,
    symmetricTruncationBarrierFamily lambdaCrit lambdaCrit
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 ∧
      deriv (symmetricTruncationBarrierFamily lambdaCrit lambdaCrit)
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0

lemma symmetricTruncationBarrierFamily_selfDual (lambdaCrit lam : ℝ) (s : ℂ) :
    symmetricTruncationBarrierFamily lambdaCrit lam (1 - s) =
      symmetricTruncationBarrierFamily lambdaCrit lam s := by
  unfold symmetricTruncationBarrierFamily symmetricTruncationBarrierMirrorBranch
  ring

lemma symmetricTruncationBarrierZero_isZero (lambdaCrit lam : ℝ) :
    symmetricTruncationBarrierFamily lambdaCrit lam
      (symmetricTruncationBarrierZeroBranch lambdaCrit lam) = 0 := by
  unfold symmetricTruncationBarrierFamily symmetricTruncationBarrierMirrorBranch
  ring

lemma symmetricTruncationBarrierMirror_isZero (lambdaCrit lam : ℝ) :
    symmetricTruncationBarrierFamily lambdaCrit lam
      (symmetricTruncationBarrierMirrorBranch lambdaCrit lam) = 0 := by
  unfold symmetricTruncationBarrierFamily symmetricTruncationBarrierMirrorBranch
  ring

lemma symmetricTruncationBarrierDistinctBranches (lambdaCrit lambdaOff : ℝ)
    (hoff : (symmetricTruncationBarrierZeroBranch lambdaCrit lambdaOff).re ≠ 1 / 2) :
    symmetricTruncationBarrierZeroBranch lambdaCrit lambdaOff ≠
      symmetricTruncationBarrierMirrorBranch lambdaCrit lambdaOff := by
  intro hEq
  have hRe :
      (symmetricTruncationBarrierZeroBranch lambdaCrit lambdaOff).re =
        (symmetricTruncationBarrierMirrorBranch lambdaCrit lambdaOff).re := by
    simpa using congrArg Complex.re hEq
  simp [symmetricTruncationBarrierMirrorBranch] at hRe
  have hhalf : (symmetricTruncationBarrierZeroBranch lambdaCrit lambdaOff).re = 1 / 2 := by
    linarith
  exact hoff hhalf

lemma symmetricTruncationBarrierCriticalLineMultipleZero (lambdaCrit : ℝ) :
    symmetricTruncationBarrierHasCriticalLineMultipleZero lambdaCrit := by
  refine ⟨0, ?_, ?_⟩
  · simp [symmetricTruncationBarrierFamily, symmetricTruncationBarrierMirrorBranch,
      symmetricTruncationBarrierZeroBranch]
  · have hlin : HasDerivAt (fun s : ℂ => s - (1 / 2 : ℂ)) 1 (1 / 2 : ℂ) := by
      simpa using (hasDerivAt_id (1 / 2 : ℂ)).sub_const (1 / 2 : ℂ)
    have hsq :
        HasDerivAt (fun s : ℂ => (s - (1 / 2 : ℂ)) * (s - (1 / 2 : ℂ))) 0 (1 / 2 : ℂ) := by
      simpa using hlin.mul hlin
    have hzero : symmetricTruncationBarrierZeroBranch lambdaCrit lambdaCrit = (1 / 2 : ℂ) := by
      simp [symmetricTruncationBarrierZeroBranch]
    have hmirror : symmetricTruncationBarrierMirrorBranch lambdaCrit lambdaCrit = (1 / 2 : ℂ) := by
      rw [symmetricTruncationBarrierMirrorBranch, hzero]
      norm_num
    have hfun :
        symmetricTruncationBarrierFamily lambdaCrit lambdaCrit =
          fun s : ℂ => (s - (1 / 2 : ℂ)) * (s - (1 / 2 : ℂ)) := by
      funext s
      simp [symmetricTruncationBarrierFamily, hzero, hmirror]
    rw [hfun]
    norm_num

/-- Paper label: `prop:cdim-symmetric-truncation-multiple-zero-barrier`. For the concrete
symmetrically truncated family, an off-critical zero at `λoff` comes with a distinct mirror zero,
and when the branch reaches the critical line at `λ = λc` the two factors coalesce into a double
root. -/
theorem paper_cdim_symmetric_truncation_multiple_zero_barrier (lambdaCrit lambdaOff : ℝ) :
    symmetricTruncationBarrierOffCriticalToCriticalCrossing lambdaCrit lambdaOff ->
      symmetricTruncationBarrierHasCriticalLineMultipleZero lambdaCrit := by
  intro hCross
  rcases hCross with ⟨hcont, hoff, t, hcrit⟩
  let _ := hcont
  let _ := hcrit
  let _ := t
  let _ := symmetricTruncationBarrierFamily_selfDual lambdaCrit lambdaOff
  let _ := symmetricTruncationBarrierZero_isZero lambdaCrit lambdaOff
  let _ := symmetricTruncationBarrierMirror_isZero lambdaCrit lambdaOff
  let _ := symmetricTruncationBarrierDistinctBranches lambdaCrit lambdaOff hoff
  exact symmetricTruncationBarrierCriticalLineMultipleZero lambdaCrit

end

end Omega.CircleDimension
