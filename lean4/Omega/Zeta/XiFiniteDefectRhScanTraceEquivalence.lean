import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite-defect data for the integrated scan-trace limit and its Fourier readout. -/
structure XiFiniteDefectRhScanTraceEquivalenceData where
  κ : ℕ
  mass : Fin κ → ℝ
  delta : Fin κ → ℝ
  scanTraceLimit : ℝ
  fourierAtZero : ℝ
  hScanTraceLimit : scanTraceLimit = ∑ j, mass j * delta j
  hFourierAtZero : fourierAtZero = 2 * Real.pi * scanTraceLimit

namespace XiFiniteDefectRhScanTraceEquivalenceData

/-- Total defect mass `Σ_j m_j δ_j`. -/
noncomputable def totalDefectMass (D : XiFiniteDefectRhScanTraceEquivalenceData) : ℝ :=
  ∑ j, D.mass j * D.delta j

/-- Concrete RH certificate used in the finite-defect package: vanishing integrated defect mass. -/
def rh (D : XiFiniteDefectRhScanTraceEquivalenceData) : Prop :=
  D.totalDefectMass = 0

/-- The boundary scan-trace limit identifies with the total defect mass. -/
def scanTraceLimitFormula (D : XiFiniteDefectRhScanTraceEquivalenceData) : Prop :=
  D.scanTraceLimit = D.totalDefectMass

/-- Vanishing of the boundary scan-trace limit. -/
def scanTraceVanishes (D : XiFiniteDefectRhScanTraceEquivalenceData) : Prop :=
  D.scanTraceLimit = 0

/-- Vanishing of the zero Fourier mode. -/
def fourierAtZeroVanishes (D : XiFiniteDefectRhScanTraceEquivalenceData) : Prop :=
  D.fourierAtZero = 0

end XiFiniteDefectRhScanTraceEquivalenceData

/-- Paper label: `thm:xi-finite-defect-rh-scan-trace-equivalence`.
The finite-defect scan-trace limit is exactly the total defect mass. In this concrete model RH is
equivalent to vanishing integrated defect, and `\widehat J(0)` vanishes exactly when the scan
trace does because `\widehat J(0) = 2π · lim_{ρ↑1} 𝒥(ρ)`. -/
theorem paper_xi_finite_defect_rh_scan_trace_equivalence
    (D : XiFiniteDefectRhScanTraceEquivalenceData) :
    D.scanTraceLimitFormula ∧
      (D.rh ↔ D.scanTraceVanishes) ∧
      (D.scanTraceVanishes ↔ D.fourierAtZeroVanishes) := by
  constructor
  · simpa [XiFiniteDefectRhScanTraceEquivalenceData.scanTraceLimitFormula,
      XiFiniteDefectRhScanTraceEquivalenceData.totalDefectMass] using D.hScanTraceLimit
  constructor
  · constructor
    · intro hRh
      simpa [XiFiniteDefectRhScanTraceEquivalenceData.rh,
        XiFiniteDefectRhScanTraceEquivalenceData.scanTraceVanishes,
        XiFiniteDefectRhScanTraceEquivalenceData.totalDefectMass] using D.hScanTraceLimit.trans hRh
    · intro hScan
      simpa [XiFiniteDefectRhScanTraceEquivalenceData.rh,
        XiFiniteDefectRhScanTraceEquivalenceData.scanTraceVanishes,
        XiFiniteDefectRhScanTraceEquivalenceData.totalDefectMass] using D.hScanTraceLimit.symm.trans hScan
  · constructor
    · intro hScan
      have hscan' : D.scanTraceLimit = 0 := hScan
      simp [XiFiniteDefectRhScanTraceEquivalenceData.fourierAtZeroVanishes, D.hFourierAtZero, hscan']
    · intro hFourier
      have hmul : 2 * Real.pi * D.scanTraceLimit = 0 := by
        simpa [XiFiniteDefectRhScanTraceEquivalenceData.fourierAtZeroVanishes, D.hFourierAtZero]
          using hFourier
      have hcoeff : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hmul).resolve_left hcoeff

end Omega.Zeta
