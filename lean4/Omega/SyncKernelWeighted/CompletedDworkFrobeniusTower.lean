import Mathlib.Tactic
import Omega.SyncKernelWeighted.CompletedPrimeCongruence
import Omega.SyncKernelWeighted.CompletedPrimitivePrimePowerDifferenceQuotient
import Omega.SyncKernelWeighted.WittFrobeniusIteratedDescent

namespace Omega.SyncKernelWeighted

open Polynomial
open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/-- Paper label: `cor:completed-dwork-frobenius-tower`. The completed prime congruence gives the
base Frobenius collapse `\hat a_p(s) ≡ s^p (mod p)`. Projecting each Dwork congruence
`\hat a_{p^j}(s) ≡ \hat a_{p^{j-1}}(s^p) (mod p^j)` to modulus `p` yields the stagewise collapse,
and iterating from the prime case gives `\hat a_{p^k}(s) ≡ s^{p^k} (mod p)`. The same inputs also
recover the completed primitive prime-power difference quotient. -/
theorem paper_completed_dwork_frobenius_tower
    (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k) (hatA : ℕ → Polynomial ℤ)
    (completedPrimitivePrime chebyshevPrime : Polynomial ℤ)
    (completedWitt completedChebyshev completedPrimitive : ℕ → ℚ)
    (hatAOne_eq_X : hatA 1 = Polynomial.X)
    (primeDifferenceWitness :
      hatA p =
        Polynomial.C (p : ℤ) * completedPrimitivePrime + (hatA 1).comp chebyshevPrime)
    (wittMatchesChebyshev : ∀ n, completedWitt n = completedChebyshev n)
    (completedMobiusPrimePowerExpansion :
      completedPrimitive (p ^ k) =
        (((ArithmeticFunction.moebius 1 : ℚ) * completedWitt (p ^ k) +
            (ArithmeticFunction.moebius p : ℚ) * completedWitt (p ^ (k - 1)) +
            Finset.sum (Finset.range (k - 1)) fun j =>
              (ArithmeticFunction.moebius (p ^ (j + 2)) : ℚ) *
                completedWitt (p ^ (k - (j + 2))))
          / (p ^ k)))
    (hchebyshev_frobenius : PolyZModEq p chebyshevPrime (Polynomial.X ^ p))
    (hdwork :
      ∀ j, 1 ≤ j →
        PolyZModEq (p ^ j) (hatA (p ^ j))
          ((hatA (p ^ (j - 1))).comp (Polynomial.X ^ p))) :
    completedPrimitive (p ^ k) =
      (completedChebyshev (p ^ k) - completedChebyshev (p ^ (k - 1))) / (p ^ k) ∧
    PolyZModEq p (hatA (p ^ k)) ((hatA (p ^ (k - 1))).comp (Polynomial.X ^ p)) ∧
    PolyZModEq p (hatA (p ^ k)) (Polynomial.X ^ (p ^ k)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  let completed_dwork_frobenius_tower_prime_data : CompletedPrimeCongruenceData :=
    { p := p
      hp := hp
      completedPrimitivePrime := completedPrimitivePrime
      hatA := hatA
      chebyshevPrime := chebyshevPrime
      hatAOne_eq_X := hatAOne_eq_X
      primeDifferenceWitness := primeDifferenceWitness }
  let completed_dwork_frobenius_tower_prime_power_data :
      CompletedPrimitivePrimePowerDifferenceQuotientData :=
    { p := p
      k := n + 1
      hp := hp
      hk := Nat.succ_le_succ (Nat.zero_le n)
      completedWitt := completedWitt
      completedChebyshev := completedChebyshev
      completedPrimitive := completedPrimitive
      wittMatchesChebyshev := wittMatchesChebyshev
      completedMobiusPrimePowerExpansion := by
        simpa [Nat.add_comm] using completedMobiusPrimePowerExpansion }
  have hquot :
      completedPrimitive (p ^ (n + 1)) =
        (completedChebyshev (p ^ (n + 1)) - completedChebyshev (p ^ n)) / (p ^ (n + 1)) := by
    simpa [CompletedPrimitivePrimePowerDifferenceQuotientData.primePowerDifferenceQuotient] using
      paper_completed_primitive_prime_power_difference_quotient
        completed_dwork_frobenius_tower_prime_power_data
  have hprime_frobenius :
      PolyZModEq p (hatA p) (Polynomial.X ^ p) := by
    exact polyZModEq_trans
      (paper_completed_prime_congruence completed_dwork_frobenius_tower_prime_data)
      hchebyshev_frobenius
  have hstage_mod_p :
      PolyZModEq p (hatA (p ^ (n + 1))) ((hatA (p ^ n)).comp (Polynomial.X ^ p)) := by
    have hdiv : p ∣ p ^ (n + 1) := dvd_pow_self p (Nat.succ_ne_zero n)
    exact polyZModEq_of_dvd hdiv (by simpa using hdwork (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
  have hpow_mod_p :
      ∀ m : ℕ, PolyZModEq p (hatA (p ^ (m + 1))) (Polynomial.X ^ (p ^ (m + 1))) := by
    intro m
    induction m with
    | zero =>
        simpa using hprime_frobenius
    | succ m ih =>
        have hstep :
            PolyZModEq p (hatA (p ^ (m + 2)))
              ((hatA (p ^ (m + 1))).comp (Polynomial.X ^ p)) := by
          have hdiv : p ∣ p ^ (m + 2) := dvd_pow_self p (Nat.succ_ne_zero (m + 1))
          exact polyZModEq_of_dvd hdiv
            (by simpa using hdwork (m + 2) (Nat.succ_le_succ (Nat.zero_le (m + 1))))
        have hcomp :
            PolyZModEq p ((hatA (p ^ (m + 1))).comp (Polynomial.X ^ p))
              (((Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 1))).comp (Polynomial.X ^ p)) := by
          exact polyZModEq_comp_right (R := Polynomial.X ^ p) ih
        have hpow :
            (((Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 1))).comp (Polynomial.X ^ p)) =
              (Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 2)) := by
          calc
            (((Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 1))).comp (Polynomial.X ^ p))
                = (Polynomial.X : Polynomial ℤ) ^ ((p ^ (m + 1)) * p) := by
                    simpa using X_pow_comp_X_pow (p ^ (m + 1)) p
            _ = (Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 2)) := by
                  simp [Nat.pow_succ', Nat.mul_comm]
        have hrefl :
            PolyZModEq p (((Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 1))).comp (Polynomial.X ^ p))
              ((Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 2))) := by
          simpa [hpow] using polyZModEq_refl p ((Polynomial.X : Polynomial ℤ) ^ (p ^ (m + 2)))
        exact polyZModEq_trans hstep (polyZModEq_trans hcomp hrefl)
  simpa [Nat.add_comm] using ⟨hquot, hstage_mod_p, hpow_mod_p n⟩

end Omega.SyncKernelWeighted
