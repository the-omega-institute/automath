import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Omega.Zeta.XiReverseKLSingleFrequencyExactMinimizer

namespace Omega.Zeta

/-- The entropy-budget feasible set for the scalar single-frequency reverse-KL proxy is exactly a
closed interval, so its supremum is the right endpoint.
    thm:xi-reversekl-single-frequency-entropy-budget-sup -/
theorem paper_xi_reversekl_single_frequency_entropy_budget_sup (n : Nat) (r h : ℝ)
    (hn : 1 ≤ n) (hr : 0 < r ∧ r < 1) (hh : 0 ≤ h) :
    sSup {c : ℝ | c ∈ Set.Icc (0 : ℝ) 1 ∧ xi_reversekl_single_frequency_inf n r c ≤ h} =
      min 1 (Real.sqrt (1 - Real.exp (-h)) / r ^ n) := by
  let α : ℝ := r ^ (2 * n)
  let s : ℝ := Real.sqrt (1 - Real.exp (-h)) / r ^ n
  let S : Set ℝ := {c : ℝ | c ∈ Set.Icc (0 : ℝ) 1 ∧ xi_reversekl_single_frequency_inf n r c ≤ h}
  have hr_pos : 0 < r := hr.1
  have hr_lt_one : r < 1 := hr.2
  have hrn_pos : 0 < r ^ n := pow_pos hr_pos n
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hα_lt_one : α < 1 := by
    dsimp [α]
    exact pow_lt_one₀ hr_pos.le hr_lt_one (by
      have hn_pos : n ≠ 0 := by omega
      omega)
  have hexp_le_one : Real.exp (-h) ≤ 1 := by
    have hneg : -h ≤ 0 := by linarith
    simpa using (Real.exp_le_exp.mpr hneg)
  have hnum_nonneg : 0 ≤ 1 - Real.exp (-h) := by
    linarith
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hr_pos.le _)
  have hpow : r ^ (2 * n) = (r ^ n) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  have hS_eq : S = Set.Icc (0 : ℝ) (min 1 s) := by
    ext c
    constructor
    · intro hc
      rcases hc with ⟨hcI, hbudget⟩
      rcases hcI with ⟨hc0, hc1⟩
      have hc_sq_le_one : c ^ 2 ≤ 1 := by
        nlinarith
      have hα_nonneg : 0 ≤ α := hα_pos.le
      have hαc_le_α : α * c ^ 2 ≤ α := by
        nlinarith
      have hinside_pos : 0 < 1 - α * c ^ 2 := by
        have hαc_lt_one : α * c ^ 2 < 1 := lt_of_le_of_lt hαc_le_α hα_lt_one
        linarith
      have hlog_ge : -h ≤ Real.log (1 - α * c ^ 2) := by
        have hbudget' : -Real.log (1 - α * c ^ 2) ≤ h := by
          simpa [α, xi_reversekl_single_frequency_inf] using hbudget
        linarith
      have hexp_le : Real.exp (-h) ≤ 1 - α * c ^ 2 :=
        (Real.le_log_iff_exp_le hinside_pos).1 hlog_ge
      have hαc_sq_le : α * c ^ 2 ≤ 1 - Real.exp (-h) := by
        linarith
      have hcr_sq_le : (c * r ^ n) ^ 2 ≤ 1 - Real.exp (-h) := by
        rw [pow_two]
        calc
          (c * r ^ n) * (c * r ^ n) = (r ^ (2 * n)) * c ^ 2 := by
            rw [hpow]
            ring
          _ = α * c ^ 2 := by rfl
          _ ≤ 1 - Real.exp (-h) := hαc_sq_le
      have hcr_nonneg : 0 ≤ c * r ^ n := mul_nonneg hc0 hrn_pos.le
      have hcr_le : c * r ^ n ≤ Real.sqrt (1 - Real.exp (-h)) := by
        have hsq : Real.sqrt (1 - Real.exp (-h)) ^ 2 = 1 - Real.exp (-h) := Real.sq_sqrt hnum_nonneg
        have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - Real.exp (-h)) := Real.sqrt_nonneg _
        nlinarith
      have hc_le_s : c ≤ s := by
        dsimp [s]
        exact (le_div_iff₀ hrn_pos).2 hcr_le
      exact ⟨hc0, le_min hc1 hc_le_s⟩
    · intro hc
      rcases hc with ⟨hc0, hcmax⟩
      have hc1 : c ≤ 1 := (le_min_iff.mp hcmax).1
      have hc_le_s : c ≤ s := (le_min_iff.mp hcmax).2
      have hcr_le : c * r ^ n ≤ Real.sqrt (1 - Real.exp (-h)) := by
        dsimp [s] at hc_le_s
        exact (le_div_iff₀ hrn_pos).mp hc_le_s
      have hαc_sq_le : α * c ^ 2 ≤ 1 - Real.exp (-h) := by
        have hsq : Real.sqrt (1 - Real.exp (-h)) ^ 2 = 1 - Real.exp (-h) := Real.sq_sqrt hnum_nonneg
        calc
          α * c ^ 2 = (r ^ (2 * n)) * c ^ 2 := by rfl
          _ = (c * r ^ n) ^ 2 := by
            rw [hpow, pow_two]
            ring
          _ ≤ Real.sqrt (1 - Real.exp (-h)) ^ 2 := by
            have hcr_nonneg : 0 ≤ c * r ^ n := mul_nonneg hc0 hrn_pos.le
            have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - Real.exp (-h)) := Real.sqrt_nonneg _
            nlinarith [hcr_le]
          _ = 1 - Real.exp (-h) := hsq
      have hinside_ge : Real.exp (-h) ≤ 1 - α * c ^ 2 := by
        linarith
      have hinside_pos : 0 < 1 - α * c ^ 2 := by
        have hexp_pos : 0 < Real.exp (-h) := Real.exp_pos (-h)
        linarith
      have hlog_ge : -h ≤ Real.log (1 - α * c ^ 2) :=
        (Real.le_log_iff_exp_le hinside_pos).2 hinside_ge
      have hbudget : -Real.log (1 - α * c ^ 2) ≤ h := by
        linarith
      refine ⟨⟨hc0, hc1⟩, ?_⟩
      simpa [α, xi_reversekl_single_frequency_inf] using hbudget
  have hIcc : (0 : ℝ) ≤ min 1 s := le_min zero_le_one hs_nonneg
  calc
    sSup S = sSup (Set.Icc (0 : ℝ) (min 1 s)) := by rw [hS_eq]
    _ = min 1 s := csSup_Icc hIcc

end Omega.Zeta
