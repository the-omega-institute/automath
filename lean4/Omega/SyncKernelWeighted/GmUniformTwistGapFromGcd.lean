import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete spectral data for the gcd obstruction package: `modulus ∤ cycleGcd` is the arithmetic
obstruction, while `twistedSpectralRadius < perronSpectralRadius` is the strict contraction
witness extracted from the twisted transfer operator. -/
structure gm_uniform_twist_gap_from_gcd_data where
  modulus : ℕ
  cycleGcd : ℕ
  perronSpectralRadius : ℝ
  twistedSpectralRadius : ℝ
  modulus_not_dvd_cycleGcd : ¬ modulus ∣ cycleGcd
  strictTwistedDrop :
    twistedSpectralRadius < perronSpectralRadius

namespace gm_uniform_twist_gap_from_gcd_data

/-- A uniform twist gap consists of the arithmetic obstruction together with an explicit positive
margin separating the twisted spectral radius from the Perron radius. -/
def has_uniform_twist_gap (D : gm_uniform_twist_gap_from_gcd_data) : Prop :=
  ¬ D.modulus ∣ D.cycleGcd ∧
    ∃ δ : ℝ, 0 < δ ∧ D.twistedSpectralRadius ≤ D.perronSpectralRadius - δ

end gm_uniform_twist_gap_from_gcd_data

open gm_uniform_twist_gap_from_gcd_data

/-- Paper label: `thm:gm-uniform-twist-gap-from-gcd`. When the modulus does not divide the cycle
gcd, the twisted operator sits a definite positive distance below the Perron radius. -/
theorem paper_gm_uniform_twist_gap_from_gcd (D : gm_uniform_twist_gap_from_gcd_data) :
    D.has_uniform_twist_gap := by
  have hgap : 0 < D.perronSpectralRadius - D.twistedSpectralRadius := by
    linarith [D.strictTwistedDrop]
  refine ⟨D.modulus_not_dvd_cycleGcd, ?_⟩
  refine ⟨(D.perronSpectralRadius - D.twistedSpectralRadius) / 2, ?_, ?_⟩
  · nlinarith
  · nlinarith

end Omega.SyncKernelWeighted
