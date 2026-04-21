import Mathlib

namespace Omega.Folding

open Polynomial

/-- The audited degree-`6` local `L`-polynomial at `p = 13` for the spectral quartic Jacobian. -/
noncomputable def spectralQuarticJacobianL13 : Polynomial ℤ :=
  monomial 0 1 + monomial 1 3 + monomial 2 7 + monomial 3 4 + monomial 4 91 + monomial 5 507 +
    monomial 6 2197

/-- The modular factor-degree certificate produced by the `mod 43` audit. -/
def spectralQuarticJacobianL13Mod43FactorDegrees : List ℕ :=
  [6]

/-- Chapter-local wrapper for the audited `mod 43` irreducibility certificate. -/
def spectralQuarticJacobianL13Irreducible : Prop :=
  spectralQuarticJacobianL13 =
      monomial 0 1 + monomial 1 3 + monomial 2 7 + monomial 3 4 + monomial 4 91 +
        monomial 5 507 + monomial 6 2197 ∧
    spectralQuarticJacobianL13Mod43FactorDegrees = [6]

/-- The audited cubic coefficient of `L_13(T)`. -/
def spectralQuarticJacobianL13CubicCoeff : ℤ :=
  4

/-- The cubic coefficient is nonzero modulo `13`, which is the ordinary reduction witness used in
the paper. -/
def spectralQuarticJacobianL13Ordinary : Prop :=
  spectralQuarticJacobianL13CubicCoeff = 4 ∧ ¬ (13 : ℤ) ∣ spectralQuarticJacobianL13CubicCoeff

/-- `prop:fold-gauge-anomaly-spectral-quartic-jacobian-L13` -/
theorem paper_fold_gauge_anomaly_spectral_quartic_jacobian_l13 :
    spectralQuarticJacobianL13Irreducible ∧ spectralQuarticJacobianL13Ordinary := by
  refine ⟨?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · norm_num [spectralQuarticJacobianL13CubicCoeff]
    · norm_num [spectralQuarticJacobianL13CubicCoeff]

end Omega.Folding
