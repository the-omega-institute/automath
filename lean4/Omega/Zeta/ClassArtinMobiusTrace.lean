import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the conjugacy-class Artin-Mobius trace
    formula in the ETDS Chebotarev section.
    cor:class-artin-mobius-trace -/
theorem paper_etds_class_artin_mobius_trace
    {Irr : Type}
    [Fintype Irr]
    [DecidableEq Irr]
    (classWeight : ℂ)
    (charCoeff primitiveCoeff channelTrace : Irr → ℂ)
    (p : ℂ)
    (hPrimitive :
      p = classWeight * ∑ ρ, charCoeff ρ * primitiveCoeff ρ)
    (hTrace : ∀ ρ, primitiveCoeff ρ = channelTrace ρ) :
    p = classWeight * ∑ ρ, charCoeff ρ * channelTrace ρ := by
  calc
    p = classWeight * ∑ ρ, charCoeff ρ * primitiveCoeff ρ := hPrimitive
    _ = classWeight * ∑ ρ, charCoeff ρ * channelTrace ρ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hTrace ρ]

end Omega.Zeta
