import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Zeta

private lemma xi_time_part62d_fiber_parity_f2_homotopy_fingerprint_fib_mod_two_eq_if
    (m : ℕ) :
    Nat.fib m % 2 = if m % 3 ≠ 0 then 1 else 0 := by
  rw [Omega.fib_mod_two_period m]
  have hlt : m % 3 < 3 := Nat.mod_lt m (by norm_num)
  interval_cases m % 3 <;> simp [Nat.fib]

/-- Paper label: `prop:xi-time-part62d-fiber-parity-f2-homotopy-fingerprint`. -/
theorem paper_xi_time_part62d_fiber_parity_f2_homotopy_fingerprint
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (ell : ι → ℕ) :
    ((∏ i ∈ I, Nat.fib (ell i + 2)) % 2 =
      if ∀ i ∈ I, (ell i + 2) % 3 ≠ 0 then 1 else 0) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Nat.mul_mod]
      have hfib :=
        xi_time_part62d_fiber_parity_f2_homotopy_fingerprint_fib_mod_two_eq_if (ell a + 2)
      by_cases haGood : (ell a + 2) % 3 ≠ 0
      · rw [if_pos haGood] at hfib
        by_cases hsGood : ∀ i ∈ s, (ell i + 2) % 3 ≠ 0
        · rw [if_pos hsGood] at ih
          have hall : ∀ i ∈ insert a s, (ell i + 2) % 3 ≠ 0 := by
            intro i hi
            rw [Finset.mem_insert] at hi
            rcases hi with rfl | hi
            · exact haGood
            · exact hsGood i hi
          rw [if_pos hall, hfib, ih]
        · rw [if_neg hsGood] at ih
          have hall : ¬ ∀ i ∈ insert a s, (ell i + 2) % 3 ≠ 0 := by
            intro h
            exact hsGood fun i hi => h i (Finset.mem_insert_of_mem hi)
          rw [if_neg hall, hfib, ih]
      · rw [if_neg haGood] at hfib
        have hall : ¬ ∀ i ∈ insert a s, (ell i + 2) % 3 ≠ 0 := by
          intro h
          exact haGood (h a (Finset.mem_insert_self a s))
        rw [if_neg hall, hfib]
        norm_num

end Omega.Zeta
