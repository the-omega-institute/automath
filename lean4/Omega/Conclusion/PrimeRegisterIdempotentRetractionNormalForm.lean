import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
import Omega.Folding.KilloPrimeRegisterIdempotentArithmetization
import Omega.Zeta.IdempotentFixedIndexStratification

namespace Omega.Conclusion

/-- The fixed-point set of a prime-register endomorphism in the finite arithmetized model. -/
def conclusion_prime_register_idempotent_retraction_normal_form_fixedPoints {n : ℕ}
    (f : Omega.Folding.PrimeRegister n) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i = i

/-- The imported finite counting package for idempotent prime-register strata. -/
def conclusion_prime_register_idempotent_retraction_normal_form_countingPackage : Prop :=
  Nat.choose 2 1 * 1 ^ 1 + Nat.choose 2 2 * 2 ^ 0 = 3 ∧
    Nat.choose 3 1 * 1 ^ 2 + Nat.choose 3 2 * 2 ^ 1 + Nat.choose 3 3 * 3 ^ 0 = 10 ∧
      Nat.choose 4 1 * 1 ^ 3 + Nat.choose 4 2 * 2 ^ 2 +
          Nat.choose 4 3 * 3 ^ 1 + Nat.choose 4 4 * 4 ^ 0 =
        41 ∧
        Nat.choose 5 1 * 1 ^ 4 + Nat.choose 5 2 * 2 ^ 3 +
            Nat.choose 5 3 * 3 ^ 2 + Nat.choose 5 4 * 4 ^ 1 + Nat.choose 5 5 * 5 ^ 0 =
          196 ∧
          2 ^ 2 = 4 ∧ 3 ^ 3 = 27

/-- Paper label: `thm:conclusion-prime-register-idempotent-retraction-normal-form`.
In the arithmetized finite prime-register model, idempotence is exactly the retraction condition
onto the fixed-point set. The theorem also records the imported finite counting package and the
factorial size of the symmetric-group maximal subgroup on a rank-`k` image. -/
def conclusion_prime_register_idempotent_retraction_normal_form_statement : Prop :=
  (∀ (n : ℕ) (f : Omega.Folding.PrimeRegister n),
      (Omega.Folding.primeRegisterMul f f = f ↔ ∀ i, f (f i) = f i) ∧
        ((∀ i, f (f i) = f i) →
          let F := conclusion_prime_register_idempotent_retraction_normal_form_fixedPoints f
          (∀ i, f i ∈ F) ∧ ∀ j ∈ F, f j = j) ∧
        (∀ F : Finset (Fin n),
          (∀ i, f i ∈ F) → (∀ j ∈ F, f j = j) → Omega.Folding.primeRegisterMul f f = f)) ∧
    conclusion_prime_register_idempotent_retraction_normal_form_countingPackage ∧
    ∀ k : ℕ, Fintype.card (Equiv.Perm (Fin k)) = Nat.factorial k

theorem paper_conclusion_prime_register_idempotent_retraction_normal_form :
    conclusion_prime_register_idempotent_retraction_normal_form_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n f
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro hmul i
        have hi := congrArg (fun g : Omega.Folding.PrimeRegister n => g i) hmul
        simpa [Omega.Folding.primeRegisterMul, Omega.Folding.primeRegisterValuation] using hi
      · intro hid
        funext i
        simpa [Omega.Folding.primeRegisterMul, Omega.Folding.primeRegisterValuation] using hid i
    · intro hid
      dsimp
      refine ⟨?_, ?_⟩
      · intro i
        simp [conclusion_prime_register_idempotent_retraction_normal_form_fixedPoints, hid i]
      · intro j hj
        simpa [conclusion_prime_register_idempotent_retraction_normal_form_fixedPoints] using hj
    · intro F himage hfix
      funext i
      simpa [Omega.Folding.primeRegisterMul, Omega.Folding.primeRegisterValuation] using
        hfix (f i) (himage i)
  · exact
      Omega.Zeta.IdempotentFixedIndexStratification.paper_xi_prime_register_idempotent_stratification_package
  · intro k
    simpa using (Fintype.card_perm (α := Fin k))

end Omega.Conclusion
