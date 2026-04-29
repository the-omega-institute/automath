import Mathlib.Tactic
import Omega.SyncKernelWeighted.CompletedPrimitivePrimePowerDifferenceQuotient
import Omega.SyncKernelWeighted.WittFrobeniusIteratedDescent

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Concrete completed prime-congruence package: the `k = 1` difference quotient is recorded by
the witness `hatA p = p * \hat p_p + \hat a_1(C_p)`, and `\hat a_1` is identified with the trace
coordinate `s`. -/
structure CompletedPrimeCongruenceData where
  p : ℕ
  hp : Nat.Prime p
  completedPrimitivePrime : Polynomial ℤ
  hatA : ℕ → Polynomial ℤ
  chebyshevPrime : Polynomial ℤ
  hatAOne_eq_X : hatA 1 = Polynomial.X
  primeDifferenceWitness :
    hatA p =
      Polynomial.C (p : ℤ) * completedPrimitivePrime + (hatA 1).comp chebyshevPrime

namespace CompletedPrimeCongruenceData

/-- The symbolic congruence `\hat a_p(s) ≡ C_p(s) (mod p)` in `ℤ[s]`. -/
def completedPrimeCongruence (D : CompletedPrimeCongruenceData) : Prop :=
  PolyZModEq D.p (D.hatA D.p) D.chebyshevPrime

end CompletedPrimeCongruenceData

open CompletedPrimeCongruenceData

/-- The `k = 1` completed primitive witness shows that `\hat a_p` is congruent modulo `p` to the
completed primitive term `\hat a_1(C_p)`. -/
theorem completed_prime_congruence_hatA_congruent_hatA1_comp
    (D : CompletedPrimeCongruenceData) :
    PolyZModEq D.p (D.hatA D.p) ((D.hatA 1).comp D.chebyshevPrime) := by
  let f : ℤ →+* ZMod D.p := Int.castRingHom (ZMod D.p)
  unfold PolyZModEq
  calc
    Polynomial.map f (D.hatA D.p) =
        Polynomial.map f
          (Polynomial.C (D.p : ℤ) * D.completedPrimitivePrime + (D.hatA 1).comp D.chebyshevPrime) := by
            rw [D.primeDifferenceWitness]
    _ = Polynomial.map f ((D.hatA 1).comp D.chebyshevPrime) := by
          simp [f]

/-- Paper label: `cor:completed-prime-congruence`. The `k = 1` completed primitive identity
shows that `\hat a_p - \hat a_1(C_p)` is divisible by `p`; after rewriting `\hat a_1(s) = s`,
this becomes the claimed congruence `\hat a_p(s) ≡ C_p(s) (mod p)`. -/
theorem paper_completed_prime_congruence (D : CompletedPrimeCongruenceData) :
    D.completedPrimeCongruence := by
  refine polyZModEq_trans (completed_prime_congruence_hatA_congruent_hatA1_comp D) ?_
  unfold PolyZModEq
  rw [D.hatAOne_eq_X]
  simp

end Omega.SyncKernelWeighted
