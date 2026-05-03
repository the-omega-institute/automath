import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

/-- Fibonacci numbers are dominated by the dyadic scale. -/
lemma xi_time_part66_macro_resonance_log_abundance_fib_le_two_pow (n : ℕ) :
    Nat.fib n ≤ 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      calc
        Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
        _ ≤ 2 ^ n + 2 ^ (n + 1) := Nat.add_le_add ih0 ih1
        _ ≤ 2 ^ (n + 2) := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
          omega

/-- The image of a dyadic-log interval under the strictly monotone tail of Fibonacci numbers has
the expected cardinality. -/
lemma xi_time_part66_macro_resonance_log_abundance_fib_image_card (a b : ℕ) :
    ((Finset.Icc a b).image fun i : ℕ => Nat.fib (i + 2)).card = (Finset.Icc a b).card := by
  exact Finset.card_image_of_injective _ Nat.fib_add_two_strictMono.injective

/-- Paper label: `thm:xi-time-part66-macro-resonance-log-abundance`. -/
theorem paper_xi_time_part66_macro_resonance_log_abundance (C : ℕ → ℝ) (cFib η : ℝ)
    (hcFib : 0 < cFib) (hη0 : 0 < η) (hη : η < cFib)
    (hFib : Tendsto (fun n : ℕ => C (Nat.fib n)) atTop (nhds cFib)) :
    ∃ Nη : ℕ, ∃ cη : ℝ, 0 < cη ∧ ∀ N : ℕ, Nη ≤ N →
      cη * Real.log (N : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun u => η ≤ C u)).card : ℝ) := by
  have _ : 0 < cFib := hcFib
  have _ : 0 < cFib := lt_trans hη0 hη
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hgood_eventually : ∀ᶠ n : ℕ in atTop, η ≤ C (Nat.fib n) := by
    have hopen : {x : ℝ | η < x} ∈ nhds cFib := Ioi_mem_nhds hη
    exact (hFib.eventually hopen).mono fun _ hlt => le_of_lt hlt
  obtain ⟨A, hA⟩ := eventually_atTop.1 hgood_eventually
  let n0 : ℕ := max A 2
  let Nη : ℕ := 2 ^ (2 * n0 + 2)
  refine ⟨Nη, 1 / (2 * Real.log (2 : ℝ)), ?_, ?_⟩
  · positivity
  intro N hN
  let L : ℕ := Nat.log 2 N
  have hNη_pos : 0 < Nη := by
    dsimp [Nη]
    positivity
  have hN_pos : 0 < N := lt_of_lt_of_le hNη_pos hN
  have hn0_ge_A : A ≤ n0 := le_max_left A 2
  have hn0_ge_two : 2 ≤ n0 := le_max_right A 2
  have hL_big : 2 * n0 + 2 ≤ L := by
    have hlog_mono : Nat.log 2 Nη ≤ Nat.log 2 N := Nat.log_mono_right hN
    have hlog_pow : Nat.log 2 Nη = 2 * n0 + 2 := by
      dsimp [Nη]
      rw [Nat.log_pow (by norm_num : 1 < 2)]
    simpa [L, hlog_pow] using hlog_mono
  have hn0_le_L : n0 ≤ L := by omega
  let S : Finset ℕ := (Finset.Icc (n0 - 2) (L - 2)).image fun i : ℕ => Nat.fib (i + 2)
  have hS_subset :
      S ⊆ (Finset.Icc 1 N).filter (fun u => η ≤ C u) := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_image] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    rw [Finset.mem_Icc] at hi
    have hn_lower : n0 ≤ i + 2 := by omega
    have hn_upper : i + 2 ≤ L := by omega
    have htwo_le_n : 2 ≤ i + 2 := by omega
    have hfib_pos : 1 ≤ Nat.fib (i + 2) := by
      exact Nat.succ_le_of_lt (Nat.fib_pos.2 (by omega))
    have hfib_le_pow : Nat.fib (i + 2) ≤ 2 ^ (i + 2) :=
      xi_time_part66_macro_resonance_log_abundance_fib_le_two_pow (i + 2)
    have hpow_le_log : 2 ^ (i + 2) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hn_upper
    have hpow_log_le_N : 2 ^ L ≤ N := by
      simpa [L] using Nat.pow_log_le_self 2 (Nat.ne_of_gt hN_pos)
    have hgood : η ≤ C (Nat.fib (i + 2)) := hA (i + 2) (le_trans hn0_ge_A hn_lower)
    exact ⟨⟨hfib_pos, le_trans hfib_le_pow (le_trans hpow_le_log hpow_log_le_N)⟩, hgood⟩
  have hcard_filter :
      (S.card : ℝ) ≤ (((Finset.Icc 1 N).filter (fun u => η ≤ C u)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hS_subset
  have hS_card : S.card = L - n0 + 1 := by
    have hcard_image :
        S.card = (Finset.Icc (n0 - 2) (L - 2)).card := by
      dsimp [S]
      exact xi_time_part66_macro_resonance_log_abundance_fib_image_card (n0 - 2) (L - 2)
    rw [hcard_image, Nat.card_Icc]
    omega
  have hcard_lower : (((L + 1 : ℕ) : ℝ) / 2) ≤ (S.card : ℝ) := by
    rw [hS_card]
    have hnat : L + 1 ≤ 2 * (L - n0 + 1) := by omega
    have hnat_real : ((L + 1 : ℕ) : ℝ) ≤ 2 * ((L - n0 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith
  have hN_lt_pow : N < 2 ^ (L + 1) := by
    simpa [L] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hN_lt_pow_real : (N : ℝ) < (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast hN_lt_pow
  have hlogN_le : Real.log (N : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((2 : ℝ) ^ (L + 1)) :=
        Real.log_le_log (by exact_mod_cast hN_pos) (le_of_lt hN_lt_pow_real)
      _ = ((L + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) := by
        rw [Real.log_pow]
  calc
    (1 / (2 * Real.log (2 : ℝ))) * Real.log (N : ℝ)
        ≤ (1 / (2 * Real.log (2 : ℝ))) *
            (((L + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)) := by
          gcongr
    _ = ((L + 1 : ℕ) : ℝ) / 2 := by
          field_simp [ne_of_gt hlog2_pos]
    _ ≤ (S.card : ℝ) := hcard_lower
    _ ≤ (((Finset.Icc 1 N).filter (fun u => η ≤ C u)).card : ℝ) := hcard_filter

end Omega.Zeta
