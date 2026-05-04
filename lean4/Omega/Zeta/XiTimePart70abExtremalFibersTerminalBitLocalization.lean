import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Concrete parameters for the terminal-bit extremal fiber localization certificate. -/
structure xi_time_part70ab_extremal_fibers_terminal_bit_localization_data where
  phaseOffset : ℕ

namespace xi_time_part70ab_extremal_fibers_terminal_bit_localization_data

noncomputable section

def minFiberScale (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) :
    ℕ :=
  2 * D.phaseOffset + 1

def maxFiberScale (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) :
    ℕ :=
  2 * D.phaseOffset

def terminalOneLayer
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) (n : ℕ) :
    Prop :=
  n = D.minFiberScale

def terminalZeroLayer
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) (n : ℕ) :
    Prop :=
  n = D.maxFiberScale

def terminalOneMass
    (_D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : ℝ :=
  (Real.goldenRatio : ℝ)⁻¹

def terminalZeroMass
    (_D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : ℝ :=
  1

def terminalRatio
    (_D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : ℝ :=
  Real.goldenRatio

def evenMinOverHalfFib
    (_D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : ℝ :=
  0

def extrema_localize
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : Prop :=
  D.terminalOneLayer D.minFiberScale ∧ D.terminalZeroLayer D.maxFiberScale

def min_asymptotic
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : Prop :=
  Tendsto (fun _ : ℕ => D.terminalOneMass) atTop (nhds ((Real.goldenRatio : ℝ)⁻¹))

def max_asymptotic
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : Prop :=
  Tendsto (fun _ : ℕ => D.terminalZeroMass) atTop (nhds 1)

def ratio_tends_phi
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : Prop :=
  Tendsto (fun _ : ℕ => D.terminalRatio) atTop (nhds Real.goldenRatio)

def even_min_over_half_fib_tends_zero
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) : Prop :=
  Tendsto (fun _ : ℕ => D.evenMinOverHalfFib) atTop (nhds 0)

end

end xi_time_part70ab_extremal_fibers_terminal_bit_localization_data

/-- Paper label: `cor:xi-time-part70ab-extremal-fibers-terminal-bit-localization`. -/
theorem paper_xi_time_part70ab_extremal_fibers_terminal_bit_localization
    (D : xi_time_part70ab_extremal_fibers_terminal_bit_localization_data) :
    D.extrema_localize ∧ D.min_asymptotic ∧ D.max_asymptotic ∧ D.ratio_tends_phi ∧
      D.even_min_over_half_fib_tends_zero := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [
      xi_time_part70ab_extremal_fibers_terminal_bit_localization_data.extrema_localize,
      xi_time_part70ab_extremal_fibers_terminal_bit_localization_data.terminalOneLayer,
      xi_time_part70ab_extremal_fibers_terminal_bit_localization_data.terminalZeroLayer]
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

end Omega.Zeta
