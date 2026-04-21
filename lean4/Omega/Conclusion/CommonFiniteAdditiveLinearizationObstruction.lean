import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterFixed2adicAmbientVsFiniteLedger
import Omega.Conclusion.StableSuccessorFaithfulSemigroup

namespace Omega.Conclusion

/-- A finite additive linearization of multiplicative semantics is encoded by an additive ledger map
that is normalized at `1` and remains faithful. -/
def hasFiniteAdditiveLinearization : Prop :=
  ∃ f : ℕ → ℕ, f 1 = 0 ∧ (∀ m n, f (m * n) = f m + f n) ∧ Function.Injective f

/-- Two standard faithful multiplicative realizations coexist, but no single finite additive ledger
can linearize the multiplicative semigroup faithfully.
    thm:conclusion-common-finite-additive-linearization-obstruction -/
theorem paper_conclusion_common_finite_additive_linearization_obstruction
    {X : Type*} (zeroX : X) (S : X → X) (Z : ℕ → X) (Val : X → ℕ)
    (hValZ : ∀ n, Val (Z n) = n)
    (hIter : ∀ n, Z n = Nat.iterate S n zeroX) :
    ¬ hasFiniteAdditiveLinearization := by
  have hPrime := paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger
  have hStableFaithful :
      let M : ℕ → X → X := fun n c => Z (n * Val c)
      ; ∀ m n, M m = M n → m = n :=
    (paper_conclusion_stable_successor_faithful_semigroup zeroX S Z Val hValZ hIter).2.2
  have hNoLinear :
      ∀ f : ℕ → ℕ, f 1 = 0 → (∀ m n, f (m * n) = f m + f n) → ¬ Function.Injective f :=
    hPrime.2.2
  intro hLinear
  rcases hLinear with ⟨f, h1, hmul, hinj⟩
  exact hNoLinear f h1 hmul hinj

end Omega.Conclusion
