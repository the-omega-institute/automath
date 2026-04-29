import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportNoRankoneAdditiveHost
import Omega.CircleDimension.SolenoidTerminalPhaseSystem

namespace Omega.CircleDimension

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Paper label: `cor:cdim-solenoid-versus-finite-additive-linearization`. This corollary simply
packages the generic-monotheticity theorem for `S`-solenoids together with the half-circle
dimension normalization and the finite-prime-support additive-host obstruction. -/
theorem paper_cdim_solenoid_versus_finite_additive_linearization
    (D : Omega.CircleDimension.SSolenoidGenericMonotheticData) (r : Nat) (hr : 2 <= r) :
    D.monothetic /\ D.generatorsDenseGdelta /\ D.generatorsFullMeasure /\
      Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.homHalfCircleDim r =
        (r : Rat) / 2 /\
      Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.implHalfCircleDim =
        (1 : Rat) / 2 /\
      (forall T : Finset Nat, ¬ (Omega.CircleDimension.finitePrimeSupportLocalizationObstruction
        r T)) := by
  rcases paper_cdim_s_solenoid_generic_monothetic D with ⟨hmono, hdense, hfull⟩
  rcases paper_xi_finite_prime_support_multiplicative_half_circle_dimension r with
    ⟨hhom, himpl, _⟩
  rcases paper_xi_finite_prime_support_no_rankone_additive_host r hr with ⟨_, _, hloc⟩
  exact ⟨hmono, hdense, hfull, hhom, himpl, hloc⟩

end Omega.CircleDimension
