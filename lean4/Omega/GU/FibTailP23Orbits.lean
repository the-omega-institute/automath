import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.GU

/-! ### Nat-level arithmetic scaffolding for the m = 6, p = 23 3-cycle orbit count. -/

/-- `F_9 = 34`.
    prop:fib-tail-p23-orbits -/
theorem fib_nine : Nat.fib 9 = 34 := by decide

/-- `2·F_9 + 1 = 69`.
    prop:fib-tail-p23-orbits -/
theorem two_fib_nine_add_one : 2 * Nat.fib 9 + 1 = 69 := by rw [fib_nine]

/-- `23 ∣ 69` (so `23 ∣ 2·F_9 + 1`; gives order 3 for the reduced fold group).
    prop:fib-tail-p23-orbits -/
theorem twentythree_dvd_sixtynine : (23 : Nat) ∣ 69 := by decide

/-- `23` is prime.
    prop:fib-tail-p23-orbits -/
theorem twentythree_prime : Nat.Prime 23 := by decide

/-- `3 ∤ 22`: cycle length 3 does not divide the non-fixed-point count.
    prop:fib-tail-p23-orbits -/
theorem three_not_dvd_twentytwo : ¬ (3 : Nat) ∣ 22 := by decide

/-- `gcd(3, 22) = 1`: the cycle length is coprime to 22.
    prop:fib-tail-p23-orbits -/
theorem gcd_three_twentytwo : Nat.gcd 3 22 = 1 := by decide

/-- `|ℙ¹(𝔽₂₃)| = 23 + 1 = 24`.
    prop:fib-tail-p23-orbits -/
theorem projective_line_f23_card : (23 : Nat) + 1 = 24 := by decide

/-- `24 = 3 · 8`.
    prop:fib-tail-p23-orbits -/
theorem twentyfour_eq_three_times_eight : (24 : Nat) = 3 * 8 := by decide

/-- Abstract orbit count (fixed-point-free): if a set of size k decomposes
    into n-element orbits, there are k/n orbits.
    prop:fib-tail-p23-orbits -/
theorem orbit_count_fixed_point_free (n k m : Nat) (hn : 0 < n) (hk : k = n * m) :
    k / n = m := by
  rw [hk]; exact Nat.mul_div_cancel_left m hn

/-- Paper-facing package of Nat-level facts underlying the m = 6, p = 23
    orbit-count proof.
    prop:fib-tail-p23-orbits -/
theorem paper_fib_tail_p23_orbits :
    Nat.fib 9 = 34 ∧
    2 * Nat.fib 9 + 1 = 69 ∧
    (23 : Nat) ∣ 69 ∧
    Nat.Prime 23 ∧
    ¬ (3 : Nat) ∣ 22 ∧
    Nat.gcd 3 22 = 1 ∧
    (23 + 1 : Nat) = 24 ∧
    (24 : Nat) = 3 * 8 ∧
    (24 : Nat) / 3 = 8 :=
  ⟨fib_nine, two_fib_nine_add_one, twentythree_dvd_sixtynine, twentythree_prime,
   three_not_dvd_twentytwo, gcd_three_twentytwo, projective_line_f23_card,
   twentyfour_eq_three_times_eight, by decide⟩

/-! ### Order-3 trace criterion: 2·F(m+3)+1 for m ∈ {4,6,8} -/

/-- Trace values: 2·F(m+3)+1 for m = 4, 6, 8.
    In PSL_2(F_p), ord(G_m) = 3 iff p | (2·F(m+3)+1).
    prop:fib-tail-order3-trace -/
theorem paper_fib_tail_order3_trace :
    2 * Nat.fib 7 + 1 = 27 ∧
    2 * Nat.fib 9 + 1 = 69 ∧
    2 * Nat.fib 11 + 1 = 179 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- 23 divides 2·F_9+1 = 69, giving order-3 at m = 6.
    prop:fib-tail-order3-trace -/
theorem twentythree_dvd_two_fib9_add1 : (23 : Nat) ∣ (2 * Nat.fib 9 + 1) := by
  rw [two_fib_nine_add_one]; exact twentythree_dvd_sixtynine

/-- 27 = 3^3: the trace value at m = 4 factors as a pure cube.
    prop:fib-tail-order3-trace -/
theorem trace_m4_eq_27 : 2 * Nat.fib 7 + 1 = 27 := by native_decide

/-- 179 is prime: the trace value at m = 8 is itself prime.
    prop:fib-tail-order3-trace -/
theorem trace_m8_prime : Nat.Prime 179 := by norm_num

/-- 179 = 2·F_11+1: combined identity.
    prop:fib-tail-order3-trace -/
theorem trace_m8_eq_179 : 2 * Nat.fib 11 + 1 = 179 := by native_decide

/-! ### BinFold escort log-fiber first and second moments -/

/-- Thermodynamic moment scaffolding: 2^6 = 64 microstates, F(8) = 21 types.
    cor:gut-foldbin-escort-logfiber-first-second-moments -/
theorem paper_gut_foldbin_escort_logfiber_first_second_moments :
    2 ^ 6 = 64 ∧ Nat.fib 8 = 21 ∧ 64 > 21 ∧
    64 - 21 = 43 ∧ 21 * 3 = 63 := by
  refine ⟨by norm_num, by native_decide, by omega, by omega, by omega⟩

end Omega.GU
