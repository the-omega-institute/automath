import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the primitive Peter--Weyl trace formula
    in the ETDS Chebotarev section.
    cor:primitive-peter-weyl-trace -/
theorem paper_etds_primitive_peter_weyl_trace
    {Irr Adams : Type}
    [Fintype Irr]
    [DecidableEq Irr]
    [Fintype Adams]
    [DecidableEq Adams]
    (primitiveCoeff : Irr → ℂ)
    (determinantContribution traceContribution : Adams → Irr → ℂ)
    (hDeterminant :
      ∀ ρ, primitiveCoeff ρ = ∑ m, determinantContribution m ρ)
    (hTrace :
      ∀ m ρ, determinantContribution m ρ = traceContribution m ρ) :
    ∀ ρ, primitiveCoeff ρ = ∑ m, traceContribution m ρ := by
  intro ρ
  calc
    primitiveCoeff ρ = ∑ m, determinantContribution m ρ := hDeterminant ρ
    _ = ∑ m, traceContribution m ρ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hTrace m ρ

end Omega.Zeta
