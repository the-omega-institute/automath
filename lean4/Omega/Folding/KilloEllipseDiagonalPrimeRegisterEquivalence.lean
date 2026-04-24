import Omega.Conclusion.PrimeRegisterEllipseCompleteEquivalence

namespace Omega.Folding

open Omega.Conclusion

/-- A diagonal integer-axis ellipse is recorded by its two positive axis parameters. -/
structure KilloDiagonalEllipse where
  majorAxis : ℕ+
  minorAxis : ℕ+

/-- Coordinatewise prime-register data for the two ellipse axes. -/
abbrev KilloPrimeRegisterPair := PrimeRegisterVector × PrimeRegisterVector

/-- The ellipse multiplication law `E_{a,b} ⊙ E_{c,d} = E_{ac,bd}`. -/
def killoEllipseMul (E F : KilloDiagonalEllipse) : KilloDiagonalEllipse :=
  ⟨E.majorAxis * F.majorAxis, E.minorAxis * F.minorAxis⟩

/-- Coordinatewise multiplication on the two prime-register vectors. -/
def killoPrimeRegisterPairMul (r s : KilloPrimeRegisterPair) : KilloPrimeRegisterPair :=
  (primeRegisterMul r.1 s.1, primeRegisterMul r.2 s.2)

/-- Send the two prime-register vectors to the corresponding diagonal ellipse axes. -/
def killoPrimeRegisterToEllipse (r : KilloPrimeRegisterPair) : KilloDiagonalEllipse :=
  ⟨primeRegisterNorm r.1, primeRegisterNorm r.2⟩

/-- Recover the two prime-register vectors from the ellipse axes via factorization. -/
def killoEllipseToPrimeRegister (E : KilloDiagonalEllipse) : KilloPrimeRegisterPair :=
  (primeRegisterOfPNat E.majorAxis, primeRegisterOfPNat E.minorAxis)

/-- Paper-facing equivalence package between coordinatewise prime registers and diagonal integer
ellipses, together with compatibility with the respective multiplication laws. -/
def killoEllipseDiagonalPrimeRegisterEquivalence : Prop :=
  Function.Bijective killoPrimeRegisterToEllipse ∧
    (∀ r : KilloPrimeRegisterPair,
      killoEllipseToPrimeRegister (killoPrimeRegisterToEllipse r) = r) ∧
    (∀ E : KilloDiagonalEllipse,
      killoPrimeRegisterToEllipse (killoEllipseToPrimeRegister E) = E) ∧
    (∀ r s : KilloPrimeRegisterPair,
      killoPrimeRegisterToEllipse (killoPrimeRegisterPairMul r s) =
        killoEllipseMul (killoPrimeRegisterToEllipse r) (killoPrimeRegisterToEllipse s))

/-- Paper label: `thm:killo-ellipse-diagonal-prime-register-equivalence`. -/
theorem paper_killo_ellipse_diagonal_prime_register_equivalence :
    killoEllipseDiagonalPrimeRegisterEquivalence := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro r s h
      cases r with
      | mk r₁ r₂ =>
        cases s with
        | mk s₁ s₂ =>
          have h₁ : primeRegisterNorm r₁ = primeRegisterNorm s₁ := by
            exact congrArg KilloDiagonalEllipse.majorAxis h
          have h₂ : primeRegisterNorm r₂ = primeRegisterNorm s₂ := by
            exact congrArg KilloDiagonalEllipse.minorAxis h
          exact Prod.ext (Nat.factorizationEquiv.symm.injective h₁)
            (Nat.factorizationEquiv.symm.injective h₂)
    · intro E
      refine ⟨killoEllipseToPrimeRegister E, ?_⟩
      cases E
      simp [killoEllipseToPrimeRegister, killoPrimeRegisterToEllipse, primeRegisterNorm,
        primeRegisterOfPNat]
  · intro r
    cases r
    exact Prod.ext (Nat.factorizationEquiv.apply_symm_apply _)
      (Nat.factorizationEquiv.apply_symm_apply _)
  · intro E
    cases E
    simp [killoEllipseToPrimeRegister, killoPrimeRegisterToEllipse, primeRegisterNorm,
      primeRegisterOfPNat]
  · intro r s
    cases r
    cases s
    simp [killoPrimeRegisterPairMul, killoPrimeRegisterToEllipse, killoEllipseMul,
      primeRegisterMul, primeRegisterNorm, primeRegisterOfPNat]
