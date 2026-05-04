import Mathlib.Tactic
import Omega.Folding.BinGaugeVolume

namespace Omega.POM

open scoped BigOperators

theorem xi_godel_integerization_log_overhead_prod_range_add_two_eq_factorial_succ
    (T : ℕ) :
    ∏ i ∈ Finset.range T, (i + 2) = Nat.factorial (T + 1) := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [Finset.prod_range_succ, ih]
      simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.factorial_succ (T + 1)).symm

theorem xi_godel_integerization_log_overhead_prod_fin_add_two_eq_factorial_succ
    (T : ℕ) :
    (∏ i : Fin T, (i.1 + 2)) = Nat.factorial (T + 1) := by
  calc
    (∏ i : Fin T, (i.1 + 2)) =
        ∏ i ∈ Finset.range T, if h : i < T then i + 2 else 1 := by
      simpa using (Finset.prod_fin_eq_prod_range (c := fun i : Fin T => i.1 + 2))
    _ = ∏ i ∈ Finset.range T, (i + 2) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = Nat.factorial (T + 1) :=
      xi_godel_integerization_log_overhead_prod_range_add_two_eq_factorial_succ T

theorem xi_godel_integerization_log_overhead_base_le_pow
    {p e : ℕ} (hp : 1 ≤ p) (he : 1 ≤ e) :
    p ≤ p ^ e := by
  rcases e with _ | e
  · omega
  · rw [Nat.pow_succ]
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right p (pow_pos (by omega : 0 < p) e)

theorem xi_godel_integerization_log_overhead_factorial_le_register_product
    {T : ℕ} (code primes : Fin T → ℕ)
    (hcode : ∀ i, 1 ≤ code i)
    (hprimes : ∀ i, i.1 + 2 ≤ primes i) :
    Nat.factorial (T + 1) ≤ Finset.univ.prod fun i : Fin T => primes i ^ code i := by
  calc
    Nat.factorial (T + 1) = ∏ i : Fin T, (i.1 + 2) := by
      symm
      exact xi_godel_integerization_log_overhead_prod_fin_add_two_eq_factorial_succ T
    _ ≤ ∏ i : Fin T, primes i ^ code i := by
      refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) ?_
      intro i _
      exact (hprimes i).trans
        (xi_godel_integerization_log_overhead_base_le_pow
          ((by omega : 1 ≤ i.1 + 2).trans (hprimes i)) (hcode i))

theorem xi_godel_integerization_log_overhead_linear_log_lower
    {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ) * Real.log T - 2 * (T : ℝ) - 1 ≤
      (T + 1 : ℝ) * Real.log (T + 1) - (T + 1 : ℝ) := by
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hT_le_succ : (T : ℝ) ≤ (T + 1 : ℝ) := by exact_mod_cast Nat.le_succ T
  have hlog_le : Real.log (T : ℝ) ≤ Real.log (T + 1 : ℝ) :=
    Real.log_le_log hT_pos hT_le_succ
  have hlog_nonneg : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hT)
  have hmul :
      (T : ℝ) * Real.log T ≤ (T + 1 : ℝ) * Real.log (T + 1) := by
    exact mul_le_mul hT_le_succ hlog_le hlog_nonneg (by positivity)
  have hsucc_cast : ((T + 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by norm_num
  nlinarith

/-- Paper label: `thm:xi-godel-integerization-log-overhead`. -/
theorem paper_xi_godel_integerization_log_overhead :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧ ∀ T : ℕ, 1 ≤ T →
      ∀ code primes : Fin T → ℕ, (∀ i, 1 ≤ code i) → (∀ i, i.1 + 2 ≤ primes i) →
        (T : ℝ) * Real.log T / Real.log 2 - c0 * T - c1 ≤
          Real.log ((Finset.univ.prod fun i : Fin T => primes i ^ code i : ℕ) : ℝ) /
            Real.log 2 := by
  refine ⟨2 / Real.log 2, 1 / Real.log 2, ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro T hT code primes hcode hprimes
  let registerProduct : ℕ := Finset.univ.prod fun i : Fin T => primes i ^ code i
  have hfactorial_le :
      Nat.factorial (T + 1) ≤ registerProduct :=
    xi_godel_integerization_log_overhead_factorial_le_register_product code primes hcode hprimes
  have hfactorial_log :
      Real.log ((Nat.factorial (T + 1) : ℕ) : ℝ) ≤ Real.log (registerProduct : ℝ) := by
    have hfac_pos : 0 < ((Nat.factorial (T + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (T + 1)
    have hfac_le : ((Nat.factorial (T + 1) : ℕ) : ℝ) ≤ (registerProduct : ℝ) := by
      exact_mod_cast hfactorial_le
    exact Real.log_le_log hfac_pos hfac_le
  have hstirling :
      (T + 1 : ℝ) * Real.log (T + 1) - (T + 1 : ℝ) ≤
        Real.log ((Nat.factorial (T + 1) : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (Omega.Folding.sub_le_log_factorial (n := T + 1) (by omega))
  have hnum :
      (T : ℝ) * Real.log T - 2 * (T : ℝ) - 1 ≤ Real.log (registerProduct : ℝ) :=
    (xi_godel_integerization_log_overhead_linear_log_lower hT).trans
      (hstirling.trans hfactorial_log)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled :
      ((T : ℝ) * Real.log T - 2 * (T : ℝ) - 1) / Real.log 2 ≤
        Real.log (registerProduct : ℝ) / Real.log 2 :=
    div_le_div_of_nonneg_right hnum (le_of_lt hlog2_pos)
  calc
    (T : ℝ) * Real.log T / Real.log 2 - (2 / Real.log 2) * T - 1 / Real.log 2 =
        ((T : ℝ) * Real.log T - 2 * (T : ℝ) - 1) / Real.log 2 := by
      ring
    _ ≤ Real.log (registerProduct : ℝ) / Real.log 2 := hscaled

end Omega.POM
