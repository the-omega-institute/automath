import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency
import Omega.TypedAddressBiaxialCompletion.NonNullRequiresThreeAxes

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local verifier package for the three-end typed-address budget closure theorem. The
fields record the three independent budget closures together with the Toeplitz--PSD side
condition, the verifier acceptance predicate, and a standardized rejection witness produced by
any failed axis. -/
structure ThreeEndBudgetData where
  radiusBudgetClosed : Prop
  addressBudgetClosed : Prop
  endpointBudgetClosed : Prop
  toeplitzPsdClosed : Prop
  verifierAccepts : Prop
  failureWitness : Prop
  accepts_of_jointClosure :
    radiusBudgetClosed →
      addressBudgetClosed →
        endpointBudgetClosed →
          toeplitzPsdClosed →
            verifierAccepts
  failure_of_radius :
    ¬ radiusBudgetClosed → failureWitness
  failure_of_address :
    ¬ addressBudgetClosed → failureWitness
  failure_of_endpoint :
    ¬ endpointBudgetClosed → failureWitness
  failure_of_toeplitz :
    ¬ toeplitzPsdClosed → failureWitness

/-- Joint closure of the radius, address, endpoint, and Toeplitz--PSD budgets forces verifier
acceptance, and any failed axis yields the standardized rejection witness.
    thm:typed-address-biaxial-completion-three-end-budget -/
theorem paper_typed_address_biaxial_completion_three_end_budget (h : ThreeEndBudgetData) :
    (h.radiusBudgetClosed ∧ h.addressBudgetClosed ∧ h.endpointBudgetClosed ∧ h.toeplitzPsdClosed →
      h.verifierAccepts) ∧
      ((¬ h.radiusBudgetClosed ∨ ¬ h.addressBudgetClosed ∨ ¬ h.endpointBudgetClosed ∨
          ¬ h.toeplitzPsdClosed) →
        h.failureWitness) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, ha, he, ht⟩
    exact h.accepts_of_jointClosure hr ha he ht
  · rintro (hr | ha | he | ht)
    · exact h.failure_of_radius hr
    · exact h.failure_of_address ha
    · exact h.failure_of_endpoint he
    · exact h.failure_of_toeplitz ht

end Omega.TypedAddressBiaxialCompletion
