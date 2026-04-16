import Omega.Zeta.ClassFunctionAdamsMobius

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the irreducible-channel determinant formula
    in the ETDS Chebotarev section.
    cor:primitive-peter-weyl-determinant -/
theorem paper_etds_primitive_peter_weyl_determinant
    {Irr Adams : Type}
    [Fintype Irr]
    [DecidableEq Irr]
    [Fintype Adams]
    [DecidableEq Adams]
    (primitiveSeries : Irr → ℂ)
    (adamsClassLog adamsDeterminantLog : Adams → Irr → ℂ)
    (adamsCoeff : Adams → Irr → Irr → ℂ)
    (traceLog determinantLog : Adams → Irr → Irr → ℂ)
    (hPrimitive : ∀ ρ, primitiveSeries ρ = ∑ m, adamsClassLog m ρ)
    (hExpand :
      ∀ m ρ, adamsClassLog m ρ = ∑ σ, adamsCoeff m ρ σ * traceLog m ρ σ)
    (hDet : ∀ m ρ σ, traceLog m ρ σ = determinantLog m ρ σ)
    (hDetLog :
      ∀ m ρ,
        adamsDeterminantLog m ρ = ∑ σ, adamsCoeff m ρ σ * determinantLog m ρ σ) :
    ∀ ρ, primitiveSeries ρ = ∑ m, adamsDeterminantLog m ρ := by
  intro ρ
  exact
    paper_etds_class_function_adams_mobius
      (primitiveSeries ρ)
      (fun m => adamsClassLog m ρ)
      (fun m => adamsDeterminantLog m ρ)
      (fun m σ => adamsCoeff m ρ σ)
      (fun m σ => traceLog m ρ σ)
      (fun m σ => determinantLog m ρ σ)
      (hPrimitive ρ)
      (fun m => hExpand m ρ)
      (fun m σ => hDet m ρ σ)
      (fun m => hDetLog m ρ)

end Omega.Zeta
