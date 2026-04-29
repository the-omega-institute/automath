import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.HzomCommutingPolarForcesCriticalLine

namespace Omega.OperatorAlgebra

/-- Normalized strip constant in the HZOM log-Sobolev certificate. -/
noncomputable def hzomLogSobolevBandConstant : ℝ := 1

/-- The zero-free strip radius extracted from the log-Sobolev constant `α`. -/
noncomputable def hzomLogSobolevBandRadius (α : ℝ) : ℝ :=
  hzomLogSobolevBandConstant / α

/-- Chapter-local encoding of the ultracontractive decay forced by the log-Sobolev constant. -/
def hzomLogSobolevDecayCertificate (α κ : ℝ) : Prop :=
  0 < α ∧ κ = Real.exp (-hzomLogSobolevBandConstant / α)

/-- Outside the band `|Re(s) - 1/2| ≤ 1/α` there are no HZOM zero events. -/
def hzomZeroFreeOutsideBand (α lam theta κ : ℝ) : Prop :=
  ∀ {σ t}, hzomLogSobolevBandRadius α < |σ - hzomCriticalAbscissa| →
    ¬ hzomCommutingPolarZeroEvent lam theta κ σ t

private theorem hzom_strictPolarContraction_of_logSobolev {α κ : ℝ}
    (hcert : hzomLogSobolevDecayCertificate α κ) :
    hzomStrictPolarContraction κ := by
  rcases hcert with ⟨hα, rfl⟩
  refine ⟨Real.exp_pos _, ?_⟩
  apply Real.exp_lt_one_iff.mpr
  have hdiv : 0 < hzomLogSobolevBandConstant / α := by
    dsimp [hzomLogSobolevBandConstant]
    exact one_div_pos.mpr hα
  have hneg : -(hzomLogSobolevBandConstant / α) < 0 := by
    linarith
  simpa [neg_div] using hneg

private theorem hzom_zeroFreeOutsideBand_of_criticalLineConcentration {α lam theta κ : ℝ}
    (hα : 0 < α) (hcritical : hzomCriticalLineConcentration lam theta κ) :
    hzomZeroFreeOutsideBand α lam theta κ := by
  intro σ t hband hzero
  have hσ : σ = hzomCriticalAbscissa := hcritical hzero
  have hradius_nonneg : 0 ≤ hzomLogSobolevBandRadius α := by
    dsimp [hzomLogSobolevBandRadius, hzomLogSobolevBandConstant]
    exact one_div_nonneg.mpr hα.le
  have hbad : hzomLogSobolevBandRadius α < 0 := by
    simpa [hσ, hzomLogSobolevBandRadius, hzomLogSobolevBandConstant] using hband
  exact (not_lt_of_ge hradius_nonneg) hbad

/-- Concrete HZOM log-Sobolev wrapper: the exponential decay parameter
`κ = exp(-1 / α)` is a strict contraction, so the commuting-polar critical-line package forces
every zero event onto `Re(s) = 1/2`; hence the band `|Re(s) - 1/2| > 1 / α` is zero-free.
    prop:op-algebra-logsobolev-zero-band -/
theorem paper_op_algebra_logsobolev_zero_band_proof {α lam theta κ : ℝ}
    (hcert : hzomLogSobolevDecayCertificate α κ)
    (hreflect : hzomReflectionSymmetricZeroSet lam theta κ) :
    hzomZeroFreeOutsideBand α lam theta κ ∧ hzomCriticalLineConcentration lam theta κ := by
  have hpackage :=
    paper_op_algebra_hzom_commuting_polar_forces_critical_line
      (hzom_strictPolarContraction_of_logSobolev hcert) hreflect
  refine ⟨hzom_zeroFreeOutsideBand_of_criticalLineConcentration hcert.1 hpackage.2, hpackage.2⟩

def paper_op_algebra_logsobolev_zero_band : Prop :=
  ∀ {α lam theta κ : ℝ},
    hzomLogSobolevDecayCertificate α κ →
      hzomReflectionSymmetricZeroSet lam theta κ →
        hzomZeroFreeOutsideBand α lam theta κ ∧ hzomCriticalLineConcentration lam theta κ

end Omega.OperatorAlgebra
