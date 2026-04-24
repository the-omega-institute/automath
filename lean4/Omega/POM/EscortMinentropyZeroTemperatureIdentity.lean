import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter

namespace Omega.POM

theorem paper_pom_escort_minentropy_zero_temperature_identity
    (Sa M : Nat → Real) (a : Nat) (Pa alphaStar : Real)
    (hSa : Tendsto (fun m : Nat => Real.log (Sa m) / (m : Real)) atTop (nhds Pa))
    (hM : Tendsto (fun m : Nat => Real.log (M m) / (m : Real)) atTop (nhds alphaStar)) :
    Tendsto
      (fun m : Nat => (Real.log (Sa m) - (a : Real) * Real.log (M m)) / (m : Real))
      atTop (nhds (Pa - (a : Real) * alphaStar)) := by
  have hScaledM :
      Tendsto
        (fun m : Nat => (a : Real) * (Real.log (M m) / (m : Real)))
        atTop (nhds ((a : Real) * alphaStar)) := by
    simpa using hM.const_mul (a : Real)
  have hSub :
      Tendsto
        (fun m : Nat => Real.log (Sa m) / (m : Real) - (a : Real) * (Real.log (M m) / (m : Real)))
        atTop (nhds (Pa - (a : Real) * alphaStar)) :=
    hSa.sub hScaledM
  have hRewrite :
      (fun m : Nat => (Real.log (Sa m) - (a : Real) * Real.log (M m)) / (m : Real)) =
        (fun m : Nat => Real.log (Sa m) / (m : Real) - (a : Real) * (Real.log (M m) / (m : Real))) := by
    funext m
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  simpa [hRewrite] using hSub

end Omega.POM
