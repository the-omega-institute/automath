import Omega.Folding.FoldPressureFreezingThreshold
import Omega.Zeta.XiFixedFreezingEscortRenyiSpectrumCollapse

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xf-frozen-phase-two-coordinate-thermodynamics`. -/
theorem paper_xi_time_part9xf_frozen_phase_two_coordinate_thermodynamics
    (D : xi_fixed_freezing_escort_renyi_spectrum_collapse_data) (P : Nat -> Real)
    (alphaStar alphaTwo gStar : Real) (a : Nat) (hgap : alphaTwo < alphaStar)
    (hLower : forall n : Nat, (n : Real) * alphaStar + gStar <= P n)
    (hUpper : forall n : Nat,
      P n <= max ((n : Real) * alphaStar + gStar)
        ((n : Real) * alphaTwo + Real.log Real.goldenRatio))
    (ha : (Real.log Real.goldenRatio - gStar) / (alphaStar - alphaTwo) < a) :
    P a = (a : Real) * alphaStar + gStar ∧
      derivedFixedFreezingTvData.massOnMaxFiber >=
        1 - Real.exp (-derivedFixedFreezingTvData.exponentialGap) ∧
      derivedFixedFreezingEntropyRateLimit D.order = derivedFixedFreezingGStar := by
  have hpressure :
      P a = (a : Real) * alphaStar + gStar :=
    Omega.Folding.paper_fold_pressure_freezing_threshold P alphaStar alphaTwo gStar a hgap
      hLower hUpper ha
  have hcollapse := paper_xi_fixed_freezing_escort_renyi_spectrum_collapse D
  rcases hcollapse with ⟨hrate, htv, htv_bound, _⟩
  have hmass :
      1 - Real.exp (-derivedFixedFreezingTvData.exponentialGap) ≤
        derivedFixedFreezingTvData.massOnMaxFiber := by
    linarith
  exact ⟨hpressure, hmass, hrate⟩

end Omega.Zeta
