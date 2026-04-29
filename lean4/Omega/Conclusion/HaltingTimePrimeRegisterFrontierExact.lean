import Mathlib.Tactic

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- Concrete data for the prime-register frontier at a finite halting time `T`. -/
structure conclusion_halting_time_prime_register_frontier_exact_data where
  halt_time : ℕ
  exponent_bound : ℕ
  register_count : ℕ
  h_exponent_bound : 1 ≤ exponent_bound
  h_register_count : 1 ≤ register_count

/-- A `(k,E)` prime-register lift is exactly the finite inequality `(E+1)^k ≥ T+1`. -/
def conclusion_halting_time_prime_register_frontier_exact_admits (T k E : ℕ) : Prop :=
  T + 1 ≤ (E + 1) ^ k

/-- The encoded base-`E+1` ceiling for the minimal register count. -/
def conclusion_halting_time_prime_register_frontier_exact_kappa (T E : ℕ) : ℕ :=
  Nat.clog (E + 1) (T + 1)

theorem conclusion_halting_time_prime_register_frontier_exact_min_exponent_ceil_exists
    (T k : ℕ) (hk : 1 ≤ k) :
    ∃ E, conclusion_halting_time_prime_register_frontier_exact_admits T k E := by
  refine ⟨T, ?_⟩
  dsimp [conclusion_halting_time_prime_register_frontier_exact_admits]
  exact le_self_pow₀ (by omega : 1 ≤ T + 1) (by omega : k ≠ 0)

/-- The encoded integer ceiling for the minimal exponent bound `E`. -/
noncomputable def conclusion_halting_time_prime_register_frontier_exact_min_exponent_ceil
    (T k : ℕ) (hk : 1 ≤ k) : ℕ :=
  Nat.find (conclusion_halting_time_prime_register_frontier_exact_min_exponent_ceil_exists T k hk)

/-- The exact frontier statement: the displayed ceilings satisfy the lift inequality and are least
with that property. -/
def conclusion_halting_time_prime_register_frontier_exact_statement
    (D : conclusion_halting_time_prime_register_frontier_exact_data) : Prop :=
  let κ :=
    conclusion_halting_time_prime_register_frontier_exact_kappa D.halt_time D.exponent_bound
  let E₀ :=
    conclusion_halting_time_prime_register_frontier_exact_min_exponent_ceil D.halt_time
      D.register_count D.h_register_count
  conclusion_halting_time_prime_register_frontier_exact_admits D.halt_time κ D.exponent_bound ∧
    (∀ j,
      conclusion_halting_time_prime_register_frontier_exact_admits D.halt_time j
          D.exponent_bound →
        κ ≤ j) ∧
    conclusion_halting_time_prime_register_frontier_exact_admits D.halt_time D.register_count E₀ ∧
    (∀ E',
      conclusion_halting_time_prime_register_frontier_exact_admits D.halt_time D.register_count E' →
        E₀ ≤ E')

/-- Paper label: `thm:conclusion-halting-time-prime-register-frontier-exact`. -/
theorem paper_conclusion_halting_time_prime_register_frontier_exact
    (D : conclusion_halting_time_prime_register_frontier_exact_data) :
    conclusion_halting_time_prime_register_frontier_exact_statement D := by
  dsimp [conclusion_halting_time_prime_register_frontier_exact_statement,
    conclusion_halting_time_prime_register_frontier_exact_kappa]
  have hbase : 1 < D.exponent_bound + 1 := Nat.lt_succ_of_le D.h_exponent_bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_pow_clog hbase (D.halt_time + 1)
  · intro j hj
    exact (Nat.clog_le_iff_le_pow hbase).2 hj
  · exact Nat.find_spec
      (conclusion_halting_time_prime_register_frontier_exact_min_exponent_ceil_exists D.halt_time
        D.register_count D.h_register_count)
  · intro E' hE'
    exact Nat.find_min'
      (conclusion_halting_time_prime_register_frontier_exact_min_exponent_ceil_exists D.halt_time
        D.register_count D.h_register_count)
      hE'

end Omega.Conclusion
