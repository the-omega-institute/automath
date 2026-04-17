import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
import Omega.CircleDimension.GodelPrimeBitlengthLowerBound
import Omega.Conclusion.PrimeRegister

namespace Omega.EA

open scoped BigOperators

private theorem prod_range_add_two_eq_factorial_succ (n : ℕ) :
    ∏ i ∈ Finset.range n, (i + 2) = Nat.factorial (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.factorial_succ (n + 1)).symm

private theorem godelEncoding_replicate_one_ge_factorial
    (primes : ℕ → ℕ) (n : ℕ) (hprime_lb : ∀ i, i < n → i + 2 ≤ primes i) :
    Nat.factorial (n + 1) ≤ Omega.Conclusion.godelEncoding primes 0 (List.replicate n 1) := by
  rw [Omega.Conclusion.godelEncoding_replicate_eq_prod]
  simp only [Nat.zero_add, pow_one]
  calc
    Nat.factorial (n + 1) = ∏ i ∈ Finset.range n, (i + 2) := by
      symm
      exact prod_range_add_two_eq_factorial_succ n
    _ ≤ ∏ i ∈ Finset.range n, primes i := by
      exact Finset.prod_le_prod
        (fun i _ => Nat.zero_le _)
        (fun i hi => hprime_lb i (Finset.mem_range.mp hi))

private theorem factorial_le_godelEncoding_of_one_event_per_slice
    (primes : ℕ → ℕ) (code : List ℕ) (hp : ∀ i, 1 < primes i)
    (hprime_lb : ∀ i, i < code.length → i + 2 ≤ primes i)
    (hcode_pos : ∀ i : Fin code.length, 1 ≤ code[i]) :
    Nat.factorial (code.length + 1) ≤ Omega.Conclusion.godelEncoding primes 0 code := by
  have hmono :
      Omega.Conclusion.godelEncoding primes 0 (List.replicate code.length 1) ≤
        Omega.Conclusion.godelEncoding primes 0 code := by
    exact Omega.Conclusion.godelEncoding_mono_of_le primes 0 (List.replicate code.length 1) code
      (by simp) hp fun i => by
        have hi : 1 ≤ code[i.val] := hcode_pos ⟨i.val, by simpa using i.isLt⟩
        simpa using hi
  exact (godelEncoding_replicate_one_ge_factorial primes code.length hprime_lb).trans hmono

/-- Paper-facing wrapper for the dynamic prime-register bitlength lower bound: one active event on
each prime slice forces the Gödel integer to dominate `(T + 1)!`, and the existing
`m log(m + 1)` bitlength infrastructure packages the asymptotic lower/upper constants.
    prop:emergent-arithmetic-dynamic-prime-register-bitlength -/
theorem paper_emergent_arithmetic_dynamic_prime_register_bitlength
    (m : ℕ) (hm : 1 ≤ m) (primes : ℕ → ℕ) (code : List ℕ) (hp : ∀ i, 1 < primes i)
    (hprime_lb : ∀ i, i < code.length → i + 2 ≤ primes i)
    (hcode_pos : ∀ i : Fin code.length, 1 ≤ code[i])
    (w : Omega.CircleDimension.GodelPrimeBitlengthWitness m) :
    Nat.factorial (code.length + 1) ≤ Omega.Conclusion.godelEncoding primes 0 code ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        c * (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) ≤ w.maxBitlength ∧
        w.maxBitlength ≤ C * (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) := by
  refine ⟨factorial_le_godelEncoding_of_one_event_per_slice primes code hp hprime_lb hcode_pos,
    ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Omega.CircleDimension.paper_cdim_godel_prime_bitlength_lowerbound m 1 hm (by omega) w

end Omega.EA
