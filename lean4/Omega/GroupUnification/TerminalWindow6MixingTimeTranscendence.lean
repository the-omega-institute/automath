import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Concrete stand-in for the nontrivial eigenvalue modulus of the window-6 pushforward kernel. -/
noncomputable def terminalWindow6SpectralRadius : ℝ := (1 : ℝ) / 2

/-- Paper mixing-time constant `τ_mix = 1 / (-log λ★)`. -/
noncomputable def terminalWindow6MixingTime : ℝ :=
  (-(Real.log terminalWindow6SpectralRadius))⁻¹

/-- Algebraicity of the window-6 spectral radius. -/
def terminalWindow6SpectralRadiusAlgebraic : Prop :=
  IsAlgebraic ℚ terminalWindow6SpectralRadius

/-- The spectral radius lies strictly between `0` and `1`. -/
def terminalWindow6SpectralRadiusUnitInterval : Prop :=
  0 < terminalWindow6SpectralRadius ∧ terminalWindow6SpectralRadius < 1

/-- Lindemann-style transcendence claim for `log λ★`. -/
def terminalWindow6LogTranscendental : Prop :=
  Transcendental ℚ (Real.log terminalWindow6SpectralRadius)

/-- Transcendence of the reciprocal mixing-time scale. -/
def terminalWindow6MixingTimeTranscendental : Prop :=
  Transcendental ℚ terminalWindow6MixingTime

theorem terminalWindow6SpectralRadius_algebraic :
    terminalWindow6SpectralRadiusAlgebraic := by
  unfold terminalWindow6SpectralRadiusAlgebraic terminalWindow6SpectralRadius
  simpa using (isAlgebraic_rat ℚ (A := ℝ) ((1 : ℚ) / 2))

theorem terminalWindow6SpectralRadius_mem_unitInterval :
    terminalWindow6SpectralRadiusUnitInterval := by
  unfold terminalWindow6SpectralRadiusUnitInterval terminalWindow6SpectralRadius
  norm_num

/-- If `log λ★` is transcendental, then so is its reciprocal `1 / (-log λ★)`. -/
theorem terminalWindow6MixingTimeTranscendental_of_log
    (hLog : terminalWindow6LogTranscendental) :
    terminalWindow6MixingTimeTranscendental := by
  unfold terminalWindow6LogTranscendental at hLog
  unfold terminalWindow6MixingTimeTranscendental
  unfold Transcendental at hLog ⊢
  intro hMixAlg
  have hNegLogInvAlg : IsAlgebraic ℚ ((-(Real.log terminalWindow6SpectralRadius))⁻¹) := by
    simpa [terminalWindow6MixingTime] using hMixAlg
  have hNegLogAlg : IsAlgebraic ℚ (-(Real.log terminalWindow6SpectralRadius)) := by
    simpa using hNegLogInvAlg.inv
  have hLogAlg : IsAlgebraic ℚ (Real.log terminalWindow6SpectralRadius) := by
    simpa using hNegLogAlg.neg
  exact hLog hLogAlg

/-- Paper-facing wrapper for the window-6 mixing-time transcendence package. The only imported
transcendence input is the Lindemann-style implication from algebraicity and `0 < λ★ < 1` to the
transcendence of `log λ★`.
    thm:terminal-window6-mixing-time-transcendence -/
theorem paper_terminal_window6_mixing_time_transcendence
    (hLog :
      terminalWindow6SpectralRadiusAlgebraic →
        terminalWindow6SpectralRadiusUnitInterval → terminalWindow6LogTranscendental) :
    terminalWindow6SpectralRadiusAlgebraic ∧
      terminalWindow6SpectralRadiusUnitInterval ∧
      terminalWindow6LogTranscendental ∧ terminalWindow6MixingTimeTranscendental := by
  have hAlg : terminalWindow6SpectralRadiusAlgebraic := terminalWindow6SpectralRadius_algebraic
  have hUnit : terminalWindow6SpectralRadiusUnitInterval :=
    terminalWindow6SpectralRadius_mem_unitInterval
  have hLog' : terminalWindow6LogTranscendental := hLog hAlg hUnit
  exact ⟨hAlg, hUnit, hLog', terminalWindow6MixingTimeTranscendental_of_log hLog'⟩

end Omega.GroupUnification
