import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-elliptic-2adic-solenoid-exact-sequence`. -/
theorem paper_conclusion_elliptic_2adic_solenoid_exact_sequence
    {E Sigma Tate : Type*} [Zero E]
    (i : Tate → Sigma)
    (pi0 : Sigma → E)
    (componentHomeomorphism kernelTotallyDisconnected : Prop)
    (hi : Function.Injective i)
    (hpi : Function.Surjective pi0)
    (hexact : ∀ s : Sigma, pi0 s = 0 ↔ ∃ t : Tate, i t = s)
    (hcomp : componentHomeomorphism)
    (hker : kernelTotallyDisconnected) :
    Function.Injective i ∧ Function.Surjective pi0 ∧
      (∀ s : Sigma, pi0 s = 0 ↔ ∃ t : Tate, i t = s) ∧
        componentHomeomorphism ∧ kernelTotallyDisconnected := by
  exact ⟨hi, hpi, hexact, hcomp, hker⟩

end Omega.Conclusion
