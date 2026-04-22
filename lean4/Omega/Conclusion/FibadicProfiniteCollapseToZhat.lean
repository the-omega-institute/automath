import Mathlib.Tactic
import Omega.Zeta.XiVisibleArithmeticFibonacciAdicProfiniteCoincidence

namespace Omega.Conclusion

open Omega.Zeta

/-- The fibadic address inverse-limit model used in the conclusion chapter. -/
abbrev FibadicAddressInverseLimit : Type := FibProfiniteCompletion

/-- The existing address inverse-limit equivalence `V_\infty`. In the chapter-local model the
address inverse limit is the same object as the Fibonacci profinite completion. -/
def fibadicAddressVInfty : FibadicAddressInverseLimit ≃+* FibProfiniteCompletion :=
  RingEquiv.refl _

/-- Concrete conclusion package: the Fibonacci moduli are cofinal, the resulting profinite
completion agrees with `\hat{\mathbf Z}`, and the address inverse limit is transported through the
same equivalence. -/
def ConclusionFibadicProfiniteCollapseToZhat : Prop :=
  FibonacciFoldModuliCofinal ∧
    Nonempty (FibProfiniteCompletion ≃+* Zhat) ∧
    Nonempty (FibadicAddressInverseLimit ≃+* Zhat)

private lemma fibadicModuliCofinal : FibonacciFoldModuliCofinal := by
  intro N hN
  exact paper_xi_visible_arithmetic_fibonacci_cofinal_quotients hN

/-- Paper label: `thm:conclusion-fibadic-profinite-collapse-to-zhat`. -/
theorem paper_conclusion_fibadic_profinite_collapse_to_zhat :
    ConclusionFibadicProfiniteCollapseToZhat := by
  have hcofinal : FibonacciFoldModuliCofinal := fibadicModuliCofinal
  refine ⟨hcofinal, ?_, ?_⟩
  · exact ⟨paper_xi_visible_arithmetic_fibonacci_adic_profinite_coincidence hcofinal⟩
  · exact
      ⟨fibadicAddressVInfty.trans
        (paper_xi_visible_arithmetic_fibonacci_adic_profinite_coincidence hcofinal)⟩

end Omega.Conclusion
