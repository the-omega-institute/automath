import Mathlib.Data.Int.Basic

namespace Omega.Conclusion

/-- Concrete obstruction package for descending local primitive spectra to a global spectrum. -/
structure conclusion_global_terminal_state_forces_global_primitive_spectrum_data where
  conclusion_global_terminal_state_forces_global_primitive_spectrum_localSpectrum : ℕ → ℤ
  conclusion_global_terminal_state_forces_global_primitive_spectrum_globalSpectrum : ℤ
  conclusion_global_terminal_state_forces_global_primitive_spectrum_cechObstruction : ℤ
  conclusion_global_terminal_state_forces_global_primitive_spectrum_syncHolonomy : ℤ

namespace conclusion_global_terminal_state_forces_global_primitive_spectrum_data

def compatibleGlobalTerminalState
    (D : conclusion_global_terminal_state_forces_global_primitive_spectrum_data) : Prop :=
  D.conclusion_global_terminal_state_forces_global_primitive_spectrum_cechObstruction = 0 ∧
    D.conclusion_global_terminal_state_forces_global_primitive_spectrum_syncHolonomy = 0 ∧
      ∀ i : ℕ,
        D.conclusion_global_terminal_state_forces_global_primitive_spectrum_localSpectrum i =
          D.conclusion_global_terminal_state_forces_global_primitive_spectrum_globalSpectrum

def localPrimitiveSpectraDescend
    (D : conclusion_global_terminal_state_forces_global_primitive_spectrum_data) : Prop :=
  ∀ i : ℕ,
    D.conclusion_global_terminal_state_forces_global_primitive_spectrum_localSpectrum i =
      D.conclusion_global_terminal_state_forces_global_primitive_spectrum_globalSpectrum

def nontrivialCechObstruction
    (D : conclusion_global_terminal_state_forces_global_primitive_spectrum_data) : Prop :=
  D.conclusion_global_terminal_state_forces_global_primitive_spectrum_cechObstruction ≠ 0

def nonzeroSyncHolonomy
    (D : conclusion_global_terminal_state_forces_global_primitive_spectrum_data) : Prop :=
  D.conclusion_global_terminal_state_forces_global_primitive_spectrum_syncHolonomy ≠ 0

end conclusion_global_terminal_state_forces_global_primitive_spectrum_data

open conclusion_global_terminal_state_forces_global_primitive_spectrum_data

/-- Paper label: `prop:conclusion-global-terminal-state-forces-global-primitive-spectrum`. -/
theorem paper_conclusion_global_terminal_state_forces_global_primitive_spectrum
    (D : conclusion_global_terminal_state_forces_global_primitive_spectrum_data) :
    D.compatibleGlobalTerminalState →
      D.localPrimitiveSpectraDescend ∧
        (D.nontrivialCechObstruction ∨ D.nonzeroSyncHolonomy →
          ¬ D.compatibleGlobalTerminalState) := by
  intro hcompat
  refine ⟨hcompat.2.2, ?_⟩
  intro hobstruction hcompat'
  rcases hobstruction with hcech | hsync
  · exact hcech hcompat'.1
  · exact hsync hcompat'.2.1

end Omega.Conclusion
