import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete residue data for
`prop:xi-basepoint-scan-van-vleck-residue-moment01`.

The finite pole-residue family records the coefficients obtained by expanding each simple
partial fraction at infinity, together with the coefficient constraints and the polewise ODE
residue identity used to read off the logarithmic derivative form. -/
structure xi_basepoint_scan_van_vleck_residue_moment01_data where
  poleCount : ℕ
  pole : Fin poleCount → ℂ
  residue : Fin poleCount → ℂ
  zInvCoefficient : ℂ
  zInvSqCoefficient : ℂ
  logDerivativeAtPole : Fin poleCount → ℂ
  odeResidueAtPole : Fin poleCount → ℂ
  partialFractionZInvCoefficient :
    zInvCoefficient = ∑ i, residue i
  infinityZInvCoefficient :
    zInvCoefficient = 0
  partialFractionZInvSqCoefficient :
    zInvSqCoefficient = ∑ i, pole i * residue i
  infinityZInvSqCoefficient :
    zInvSqCoefficient = 0
  odeResidueIdentity :
    ∀ i, logDerivativeAtPole i = odeResidueAtPole i

namespace xi_basepoint_scan_van_vleck_residue_moment01_data

/-- The vanishing of the `z⁻¹` coefficient at infinity gives the total-residue balance. -/
def moment0_balance (D : xi_basepoint_scan_van_vleck_residue_moment01_data) : Prop :=
  ∑ i, D.residue i = 0

/-- The vanishing of the `z⁻²` coefficient at infinity gives the first pole moment balance. -/
def moment1_balance (D : xi_basepoint_scan_van_vleck_residue_moment01_data) : Prop :=
  ∑ i, D.pole i * D.residue i = 0

/-- The recorded ODE residue identity, expressed as the logarithmic derivative at every pole. -/
def ode_residue_form (D : xi_basepoint_scan_van_vleck_residue_moment01_data) : Prop :=
  ∀ i, D.logDerivativeAtPole i = D.odeResidueAtPole i

end xi_basepoint_scan_van_vleck_residue_moment01_data

/-- Paper label: `prop:xi-basepoint-scan-van-vleck-residue-moment01`. -/
theorem paper_xi_basepoint_scan_van_vleck_residue_moment01
    (D : xi_basepoint_scan_van_vleck_residue_moment01_data) :
    D.moment0_balance ∧ D.moment1_balance ∧ D.ode_residue_form := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      ∑ i, D.residue i = D.zInvCoefficient := D.partialFractionZInvCoefficient.symm
      _ = 0 := D.infinityZInvCoefficient
  · calc
      ∑ i, D.pole i * D.residue i = D.zInvSqCoefficient :=
        D.partialFractionZInvSqCoefficient.symm
      _ = 0 := D.infinityZInvSqCoefficient
  · exact D.odeResidueIdentity

end Omega.Zeta
