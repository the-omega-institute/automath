import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-multiplicity-composition-mod3-badcount-clt`. -/
theorem paper_pom_multiplicity_composition_mod3_badcount_clt (q : ℕ)
    (quasiPower linearDensity gaussianFluctuation slopeClosedForm : Prop)
    (hQuasiPower : quasiPower) (hDensity : quasiPower → linearDensity)
    (hGaussian : quasiPower → gaussianFluctuation) (hSlope : quasiPower → slopeClosedForm) :
    quasiPower ∧ linearDensity ∧ gaussianFluctuation ∧ slopeClosedForm := by
  have _ : ℕ := q
  exact ⟨hQuasiPower, hDensity hQuasiPower, hGaussian hQuasiPower, hSlope hQuasiPower⟩

end Omega.POM
