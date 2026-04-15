import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
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

private theorem cube_eq_one_of_trace_neg_one_det_one
    (M : Matrix (Fin 2) (Fin 2) (ZMod 23))
    (htrace : Matrix.trace M = (-1 : ZMod 23))
    (hdet : M.det = (1 : ZMod 23)) :
    M ^ 3 = 1 := by
  let a : ZMod 23 := M 0 0
  let b : ZMod 23 := M 0 1
  let c : ZMod 23 := M 1 0
  let d : ZMod 23 := M 1 1
  have htr : a + d = (-1 : ZMod 23) := by
    simpa [a, d, Matrix.trace_fin_two] using htrace
  have hde : a * d - b * c = (1 : ZMod 23) := by
    simpa [a, b, c, d, Matrix.det_fin_two] using hdet
  have hbc : b * c = a * d - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hde).symm
  have hcb : c * b = a * d - 1 := by
    simpa [mul_comm] using hbc
  have hsum : a + d + 1 = 0 := by
    rw [htr]
    norm_num
  have hquad : M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23)) = 0 := by
    ext i j <;> fin_cases i <;> fin_cases j
    · calc
        ((M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) 0 0)
            = (M ^ 2) 0 0 + M 0 0 + 1 := by
                simp
        _ = a * a + b * c + a + 1 := by
              rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        _ = a * a + (a * d - 1) + a + 1 := by rw [hbc]
        _ = a * (a + d + 1) := by ring
        _ = 0 := by rw [hsum]; ring
    · calc
        ((M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) 0 1)
            = (M ^ 2) 0 1 + M 0 1 := by
                simp
        _ = a * b + b * d + b := by
              rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        _ = b * (a + d + 1) := by ring
        _ = 0 := by rw [hsum]; ring
    · calc
        ((M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) 1 0)
            = (M ^ 2) 1 0 + M 1 0 := by
                simp
        _ = c * a + d * c + c := by
              rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        _ = c * (a + d + 1) := by ring
        _ = 0 := by rw [hsum]; ring
    · calc
        ((M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) 1 1)
            = (M ^ 2) 1 1 + M 1 1 + 1 := by
                simp
        _ = c * b + d * d + d + 1 := by
              rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        _ = (a * d - 1) + d * d + d + 1 := by rw [hcb]
        _ = d * (a + d + 1) := by ring
        _ = 0 := by rw [hsum]; ring
  have hmul : (M ^ 2 + M + 1) * (M - 1) = M ^ 3 - 1 := by
    calc
      (M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) * (M - 1)
          = (M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) * M -
              (M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) := by
              rw [Matrix.mul_sub, Matrix.mul_one]
      _ = (M ^ 2 * M + M * M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23)) * M) -
            (M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) (ZMod 23))) := by
              rw [add_mul, add_mul]
      _ = (M ^ 2 * M + M ^ 2 + M) - (M ^ 2 + M + 1) := by
            rw [pow_two, Matrix.one_mul]
      _ = M ^ 2 * M - 1 := by
            abel
      _ = M ^ 3 - 1 := by
            simp [pow_one, pow_two, pow_succ, Matrix.mul_assoc]
  have hzero : (M ^ 2 + M + 1) * (M - 1) = 0 := by
    simp [hquad]
  rw [hmul] at hzero
  exact sub_eq_zero.mp hzero

private theorem prime_dvd_two_fib9_add1_iff_eq_twentythree {p : Nat}
    (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    p ∣ (2 * Nat.fib 9 + 1) ↔ p = 23 := by
  rw [two_fib_nine_add_one]
  constructor
  · intro hdiv
    have hmul : p ∣ 3 * 23 := by simpa using hdiv
    rcases hp.dvd_mul.mp hmul with h3 | h23
    · exfalso
      have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3
      exact hp3 this
    · exact (Nat.prime_dvd_prime_iff_eq hp twentythree_prime).mp h23
  · intro hp23
    rw [hp23]
    exact twentythree_dvd_two_fib9_add1

/-- Window-6 hyperbolic tail matrices degenerate to order `3` modulo `23`:
the reduced matrix satisfies `Ā^3 = 1`, is not the identity, and `23` is the
unique prime `p ≠ 3` dividing `2·F_9+1`.
    cor:terminal-window6-sl2-mod23-order3 -/
theorem paper_terminal_window6_sl2_mod23_order3 :
    ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      Matrix.trace A = 68 →
      A.det = 1 →
      ((A 0 1 : ZMod 23) = 21) →
      let Abar : Matrix (Fin 2) (Fin 2) (ZMod 23) := A.map (Int.castRingHom (ZMod 23))
      Abar ^ 3 = 1 ∧
      Abar ≠ 1 ∧
      (23 : Nat) ∣ (2 * Nat.fib 9 + 1) ∧
      (∀ p : Nat, Nat.Prime p → p ≠ 3 →
        (p ∣ (2 * Nat.fib 9 + 1) ↔ p = 23)) := by
  intro A htrace hdet h01
  dsimp
  let Abar : Matrix (Fin 2) (Fin 2) (ZMod 23) := A.map (Int.castRingHom (ZMod 23))
  have htrace_bar : Matrix.trace Abar = (-1 : ZMod 23) := by
    have hcast : ((Matrix.trace A : ℤ) : ZMod 23) = (-1 : ZMod 23) := by
      rw [htrace]
      decide
    simpa [Abar, Matrix.trace_fin_two] using hcast
  have hdet_bar : Abar.det = (1 : ZMod 23) := by
    simpa [Abar, Matrix.det_fin_two] using congrArg (fun z : ℤ => (z : ZMod 23)) hdet
  have hAbar_ne : Abar ≠ 1 := by
    have h21neq0 : (21 : ZMod 23) ≠ 0 := by decide
    intro hAbar
    have hentry : Abar 0 1 = (21 : ZMod 23) := by
      simpa [Abar] using h01
    have hzero : Abar 0 1 = 0 := by
      simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 23) => M 0 1) hAbar
    rw [hentry] at hzero
    exact h21neq0 hzero
  refine ⟨cube_eq_one_of_trace_neg_one_det_one Abar htrace_bar hdet_bar, hAbar_ne,
    twentythree_dvd_two_fib9_add1, ?_⟩
  intro p hp hp3
  exact prime_dvd_two_fib9_add1_iff_eq_twentythree hp hp3

end Omega.GU
