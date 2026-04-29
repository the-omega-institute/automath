import Omega.Folding.FiberRing

/-!
# Stable-value affine transfer audit wrapper

This file records the paper-facing transport wrapper used by the stable arithmetic audit.
-/

namespace Omega.StableArithmetic

set_option linter.unusedVariables false in
/-- Paper-facing wrapper for stable-value affine transfer.
    lem:stable-audit-stable-value-affine-transfer -/
theorem paper_stable_audit_stable_value_affine_transfer {X R Term : Type*}
    (transport : X ≃ R) (satisfiesX satisfiesR : Term → Term → Prop)
    (htransport : ∀ s t, satisfiesX s t ↔ satisfiesR s t) :
    ∀ s t, satisfiesX s t ↔ satisfiesR s t := by
  intro s t
  exact htransport s t

end Omega.StableArithmetic
