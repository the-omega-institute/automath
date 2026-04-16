import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for the Jensen defect finiteization interface: the defect is a scalar
radius certificate, while `zeroFree` records the corresponding zero-free condition on that radius
layer. -/
structure JensenDefectFiniteizationData where
  defect : Real → Real
  zeroFree : Real → Prop
  semantics :
      ∀ rho : Real, 0 < rho → rho < 1 →
        0 ≤ defect rho ∧ (defect rho = 0 ↔ zeroFree rho)

/-- Paper-facing proposition: the Jensen defect is nonnegative and vanishes exactly when the
corresponding radius layer is zero-free.
    prop:typed-address-biaxial-completion-jensen-defect-finiteization -/
theorem paper_typed_address_biaxial_completion_jensen_defect_finiteization
    (h : JensenDefectFiniteizationData) :
    forall {rho : Real}, 0 < rho -> rho < 1 -> 0 <= h.defect rho /\ (h.defect rho = 0 <-> h.zeroFree rho) := by
  intro rho hrho hrho_lt
  exact h.semantics rho hrho hrho_lt

end Omega.TypedAddressBiaxialCompletion
