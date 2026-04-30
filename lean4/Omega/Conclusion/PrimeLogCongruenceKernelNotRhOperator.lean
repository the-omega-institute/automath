import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-prime-log-congruence-kernel-not-rh-operator`. -/
theorem paper_conclusion_prime_log_congruence_kernel_not_rh_operator
    {Kernel : Type*} (carriesPrimeLog satisfiesRHGate : Kernel → Prop)
    (hneeded : ∀ K, satisfiesRHGate K → carriesPrimeLog K) (K : Kernel)
    (hmissing : Not (carriesPrimeLog K)) :
    Not (satisfiesRHGate K) := by
  intro hgate
  exact hmissing (hneeded K hgate)

end Omega.Conclusion
