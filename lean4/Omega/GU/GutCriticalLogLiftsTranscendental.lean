import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The six critical algebraic scales in the simplified GUT model. -/
def gutCriticalParameter : Fin 6 → ℝ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 11
  | ⟨5, _⟩ => 13

/-- Any chosen logarithm branch of the six critical scales. -/
noncomputable def gutCriticalLogLift (i : Fin 6) : ℝ :=
  Real.log (gutCriticalParameter i)

/-- The Lindemann-style input used in the paper: the logarithm of a nonzero algebraic number
different from `1` is transcendental. -/
def GutCriticalLindemannInput : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → α ≠ 0 → α ≠ 1 → Transcendental ℚ (Real.log α)

private theorem gutCriticalParameter_algebraic (i : Fin 6) :
    IsAlgebraic ℚ (gutCriticalParameter i) := by
  fin_cases i
  · simpa [gutCriticalParameter] using (isAlgebraic_rat ℚ (A := ℝ) (2 : ℚ))
  · simpa [gutCriticalParameter] using (isAlgebraic_rat ℚ (A := ℝ) (3 : ℚ))
  · simpa [gutCriticalParameter] using (isAlgebraic_rat ℚ (A := ℝ) (5 : ℚ))
  · simpa [gutCriticalParameter] using (isAlgebraic_rat ℚ (A := ℝ) (7 : ℚ))
  · simpa [gutCriticalParameter] using (isAlgebraic_rat ℚ (A := ℝ) (11 : ℚ))
  · simpa [gutCriticalParameter] using (isAlgebraic_rat ℚ (A := ℝ) (13 : ℚ))

private theorem gutCriticalParameter_ne_zero (i : Fin 6) :
    gutCriticalParameter i ≠ 0 := by
  fin_cases i <;> norm_num [gutCriticalParameter]

private theorem gutCriticalParameter_ne_one (i : Fin 6) :
    gutCriticalParameter i ≠ 1 := by
  fin_cases i <;> norm_num [gutCriticalParameter]

/-- Paper label: `cor:gut-critical-log-lifts-transcendental`. -/
theorem paper_gut_critical_log_lifts_transcendental
    (hLindemann : GutCriticalLindemannInput) :
    ∀ i : Fin 6, Transcendental ℚ (gutCriticalLogLift i) := by
  intro i
  exact hLindemann (gutCriticalParameter i) (gutCriticalParameter_algebraic i)
    (gutCriticalParameter_ne_zero i) (gutCriticalParameter_ne_one i)

end Omega.GU
