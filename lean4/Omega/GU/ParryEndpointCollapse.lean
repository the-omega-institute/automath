import Omega.GroupUnification.ParryEndpointCollapse

namespace Omega.GU.ParryEndpointCollapse

variable {α : Type*}

/-- Paper-facing `GU` wrapper for the Parry endpoint collapse theorem.
    thm:parry-endpoint-collapse -/
theorem paper_parry_endpoint_collapse
    (π : α → ℝ) (P : α → α → ℝ) (ℓ r : α → ℝ) (lam Z : ℝ)
    (hπ : ∀ a, π a = ℓ a * r a / Z)
    (hP : ∀ a b, P a b = r b / (lam * r a))
    (hlam : lam ≠ 0) (hZ : Z ≠ 0) (hr : ∀ a, r a ≠ 0)
    (a : α) (u : List α) :
    Omega.GroupUnification.ParryEndpointCollapse.cylinderWeight π P (a :: u) =
      ℓ a * r (List.getLast (a :: u) (by simp)) / (Z * lam ^ u.length) := by
  simpa using
    Omega.GroupUnification.ParryEndpointCollapse.paper_parry_endpoint_collapse
      π P ℓ r lam Z hπ hP hlam hZ hr a u

end Omega.GU.ParryEndpointCollapse
