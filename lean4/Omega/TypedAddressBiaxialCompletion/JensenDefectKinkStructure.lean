import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.JensenDefectLogDerivative

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete left/right log-slope bookkeeping for the Jensen defect at each radius. The count
functions encode the zero-count just below and just above the shell, while `shellMultiplicity`
records the multiplicity supported exactly on that shell. -/
structure JensenDefectKinkProfile where
  defect : ℝ → ℝ
  leftCount : ℝ → ℕ
  rightCount : ℝ → ℕ
  shellMultiplicity : ℝ → ℕ
  leftLogSlope : ℝ → ℝ
  rightLogSlope : ℝ → ℝ
  leftLogSlope_eq_count : ∀ r, leftLogSlope r = (leftCount r : ℝ)
  rightLogSlope_eq_count : ∀ r, rightLogSlope r = (rightCount r : ℝ)
  shell_jump : ∀ r, rightCount r = leftCount r + shellMultiplicity r

namespace JensenDefectKinkProfile

/-- The slope jump of the Jensen defect viewed as a function of `log ρ`. -/
def slopeJump (J : JensenDefectKinkProfile) (r : ℝ) : ℝ :=
  J.rightLogSlope r - J.leftLogSlope r

/-- The jump in the zero-counting function across the shell `|a| = r`. -/
def countJump (J : JensenDefectKinkProfile) (r : ℝ) : ℕ :=
  J.rightCount r - J.leftCount r

/-- The shell forces a genuine kink exactly when it carries nonzero multiplicity. -/
def hasKink (J : JensenDefectKinkProfile) (r : ℝ) : Prop :=
  J.rightLogSlope r ≠ J.leftLogSlope r

lemma countJump_eq_shellMultiplicity (J : JensenDefectKinkProfile) (r : ℝ) :
    J.countJump r = J.shellMultiplicity r := by
  have hjump := J.shell_jump r
  unfold countJump
  omega

lemma slopeJump_eq_shellMultiplicity (J : JensenDefectKinkProfile) (r : ℝ) :
    J.slopeJump r = (J.shellMultiplicity r : ℝ) := by
  have hright :
      (J.rightCount r : ℝ) = (J.leftCount r : ℝ) + (J.shellMultiplicity r : ℝ) := by
    exact_mod_cast J.shell_jump r
  unfold slopeJump
  rw [J.rightLogSlope_eq_count r, J.leftLogSlope_eq_count r, hright]
  ring

lemma hasKink_iff_shellMultiplicity_pos (J : JensenDefectKinkProfile) (r : ℝ) :
    J.hasKink r ↔ J.shellMultiplicity r ≠ 0 := by
  constructor
  · intro hk hzero
    apply hk
    have hslope : J.slopeJump r = 0 := by
      simpa [J.slopeJump_eq_shellMultiplicity r, hzero]
    unfold slopeJump at hslope
    exact sub_eq_zero.mp hslope
  · intro hmult hEq
    have hslope : J.slopeJump r = 0 := by
      unfold slopeJump
      rw [hEq]
      ring
    have hmult_zero : J.shellMultiplicity r = 0 := by
      rw [J.slopeJump_eq_shellMultiplicity r] at hslope
      exact_mod_cast hslope
    exact hmult hmult_zero

end JensenDefectKinkProfile

open JensenDefectKinkProfile

/-- The left/right log-derivative laws identify the slope jump with the shell multiplicity, hence
the zero-count jump equals the same multiplicity and the defect acquires a genuine kink exactly
when the shell is nonempty.
    cor:app-jensen-defect-kink-structure -/
theorem paper_app_jensen_defect_kink_structure
    (J : JensenDefectKinkProfile) (r : ℝ) :
    J.slopeJump r = (J.shellMultiplicity r : ℝ) ∧
      J.countJump r = J.shellMultiplicity r ∧
      (J.hasKink r ↔ J.shellMultiplicity r ≠ 0) := by
  exact ⟨J.slopeJump_eq_shellMultiplicity r, J.countJump_eq_shellMultiplicity r,
    J.hasKink_iff_shellMultiplicity_pos r⟩

end Omega.TypedAddressBiaxialCompletion
