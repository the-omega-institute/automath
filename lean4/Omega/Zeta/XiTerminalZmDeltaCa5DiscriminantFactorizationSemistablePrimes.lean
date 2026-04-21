import Mathlib.Tactic

namespace Omega.Zeta

/-- The discriminant of the quintic `B₅`. -/
def xiTerminalZmDeltaCa5DiscB5 : ℤ :=
  -((2 : ℤ) ^ 16 * 3 ^ 16 * 17 ^ 3 * 37 * 223 ^ 3 * 3739 ^ 2 * 7333 ^ 2)

/-- The special value `B₅(4)` appearing in the branch-collision factor. -/
def xiTerminalZmDeltaCa5B5At4 : ℤ :=
  (2 : ℤ) ^ 6 * 3 ^ 4 * 11 ^ 3 * 13

/-- The discriminant of `f(δ) = (δ - 4) B₅(δ)`. -/
def xiTerminalZmDeltaCa5CurveDisc : ℤ :=
  -((2 : ℤ) ^ 28 * 3 ^ 24 * 11 ^ 6 * 13 ^ 2 * 17 ^ 3 * 37 * 223 ^ 3 * 3739 ^ 2 * 7333 ^ 2)

/-- Collision primes coming from double roots of `B₅ mod p`. -/
def xiTerminalZmDeltaCa5CollisionPrimes : Finset ℕ :=
  {17, 37, 223, 3739, 7333}

/-- Branch-collision primes coming from `δ = 4`. -/
def xiTerminalZmDeltaCa5BranchCollisionPrimes : Finset ℕ :=
  {11, 13}

/-- The odd semistable primes of the genus-two quotient. -/
def xiTerminalZmDeltaCa5OddSemistablePrimes : Finset ℕ :=
  xiTerminalZmDeltaCa5CollisionPrimes ∪ xiTerminalZmDeltaCa5BranchCollisionPrimes

/-- The discriminant factorization `Disc ((δ - 4) B₅(δ)) = Disc(B₅) * B₅(4)^2`. -/
def xiTerminalZmDeltaCa5DiscriminantFactorization : Prop :=
  xiTerminalZmDeltaCa5CurveDisc = xiTerminalZmDeltaCa5DiscB5 * xiTerminalZmDeltaCa5B5At4 ^ 2

/-- The explicit special value and the explicit discriminant factorization recorded in the paper. -/
def xiTerminalZmDeltaCa5ExplicitDiscriminant : Prop :=
  xiTerminalZmDeltaCa5B5At4 = 89698752 ∧
    xiTerminalZmDeltaCa5CurveDisc =
      -((2 : ℤ) ^ 28 * 3 ^ 24 * 11 ^ 6 * 13 ^ 2 * 17 ^ 3 * 37 *
        223 ^ 3 * 3739 ^ 2 * 7333 ^ 2)

/-- The odd semistable prime set is exactly the five collision primes together with the two
branch-collision primes at `δ = 4`. -/
def xiTerminalZmDeltaCa5OddSemistablePrimeCharacterization : Prop :=
  xiTerminalZmDeltaCa5OddSemistablePrimes = {11, 13, 17, 37, 223, 3739, 7333}

/-- Paper label: `prop:xi-terminal-zm-delta-ca5-discriminant-factorization-semistable-primes`.
This packages the explicit integer factorization and the resulting odd semistable prime set. -/
theorem paper_xi_terminal_zm_delta_ca5_discriminant_factorization_semistable_primes :
    xiTerminalZmDeltaCa5DiscriminantFactorization ∧
      xiTerminalZmDeltaCa5ExplicitDiscriminant ∧
      xiTerminalZmDeltaCa5OddSemistablePrimeCharacterization := by
  refine ⟨?_, ?_, ?_⟩
  · unfold xiTerminalZmDeltaCa5DiscriminantFactorization
    native_decide
  · refine ⟨by native_decide, rfl⟩
  · unfold xiTerminalZmDeltaCa5OddSemistablePrimeCharacterization
    native_decide

end Omega.Zeta
