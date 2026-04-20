import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

private lemma sqrt_natPow_eq_exp_half_log (c : Real) (hc : 0 < c) (q : Nat) :
    Real.sqrt (c ^ q) = Real.exp ((Real.log c / 2) * q) := by
  have hc_nonneg : 0 ≤ c := hc.le
  calc
    Real.sqrt (c ^ q) = (c ^ q) ^ (1 / (2 : Real)) := by
      rw [Real.sqrt_eq_rpow]
    _ = (c ^ (q : Real)) ^ (1 / (2 : Real)) := by
      rw [← Real.rpow_natCast]
    _ = c ^ ((q : Real) * (1 / (2 : Real))) := by
      rw [Real.rpow_mul hc_nonneg]
    _ = c ^ ((q : Real) / 2) := by
      congr 1
      ring
    _ = (Real.exp (Real.log c)) ^ ((q : Real) / 2) := by
      rw [Real.exp_log hc]
    _ = Real.exp (Real.log c * ((q : Real) / 2)) := by
      rw [← Real.exp_mul]
    _ = Real.exp ((Real.log c / 2) * q) := by
      congr 1
      ring

private lemma squeeze_profile_eq (c : Real) (hc : 0 < c) (q : Nat) :
    2 * Real.exp ((Real.log c / 4) * q) / Real.sqrt (c ^ q) =
      2 * Real.exp (-(Real.log c / 4) * q) := by
  rw [sqrt_natPow_eq_exp_half_log c hc q, div_eq_mul_inv, ← Real.exp_neg]
  rw [mul_assoc]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

private lemma two_le_eps_mul_nat (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ q ≥ N, (2 : Real) ≤ eps * q := by
  refine ⟨⌈2 / eps⌉₊, ?_⟩
  intro q hq
  have hq' : (2 / eps : Real) ≤ q := by
    calc
      (2 / eps : Real) ≤ ⌈2 / eps⌉₊ := Nat.le_ceil _
      _ ≤ q := by exact_mod_cast hq
  have hmul := (div_le_iff₀ heps).mp hq'
  simpa [mul_comm] using hmul

/-- Under an RH-style squeeze and exponential residue-scale lower bound, the finite-part residue
drift is eventually bounded by any linear `ε q` tail. -/
theorem paper_finite_part_residue_drift_trichotomy (rho d C : Nat → Real) (c : Real)
    (hc : 1 < c) (hrho_pos : ∃ N, ∀ q ≥ N, 0 < rho q) (hC_pos : ∃ N, ∀ q ≥ N, 0 < C q)
    (hrho : ∃ N, ∀ q ≥ N, c ^ q ≤ rho q)
    (hd : ∀ eps > 0, ∃ N, ∀ q ≥ N, d q ≤ Real.exp (eps * (q : Real)))
    (hsqueeze : ∃ N, ∀ q ≥ N, |Real.log (C q)| ≤ 2 * d q / Real.sqrt (rho q)) :
    ∀ eps > 0, ∃ N, ∀ q ≥ N, |Real.log (C q)| ≤ eps * (q : Real) := by
  let _ := hrho_pos
  let _ := hC_pos
  intro eps heps
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  have hlogc_pos : 0 < Real.log c := Real.log_pos hc
  let a : Real := Real.log c / 4
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  obtain ⟨Nρ, hρ⟩ := hrho
  obtain ⟨Nd, hd'⟩ := hd a ha_pos
  obtain ⟨Ns, hsq⟩ := hsqueeze
  obtain ⟨Nlin, hlin⟩ := two_le_eps_mul_nat eps heps
  refine ⟨max (max (max Nρ Nd) Ns) Nlin, ?_⟩
  intro q hq
  have hqleft : max (max Nρ Nd) Ns ≤ q := le_trans (le_max_left _ _) hq
  have hqmid : max Nρ Nd ≤ q := le_trans (le_max_left _ _) hqleft
  have hqρ : q ≥ Nρ := le_trans (le_max_left _ _) hqmid
  have hqd : q ≥ Nd := le_trans (le_max_right _ _) hqmid
  have hqs : q ≥ Ns := le_trans (le_max_right _ _) hqleft
  have hqlin : q ≥ Nlin := le_trans (le_max_right _ _) hq
  have hrhoq : c ^ q ≤ rho q := hρ q hqρ
  have hdq : d q ≤ Real.exp (a * q) := by
    simpa [a, mul_comm, mul_left_comm, mul_assoc] using hd' q hqd
  have hrhoq_pos : 0 < rho q := by
    have hcq_pos : 0 < c ^ q := pow_pos hc_pos q
    exact lt_of_lt_of_le hcq_pos hrhoq
  have hsqrt_le : Real.sqrt (c ^ q) ≤ Real.sqrt (rho q) := Real.sqrt_le_sqrt hrhoq
  have hbound :
      2 * d q / Real.sqrt (rho q) ≤ 2 * Real.exp (a * q) / Real.sqrt (c ^ q) := by
    gcongr
  have hdecay :
      2 * Real.exp (a * q) / Real.sqrt (c ^ q) = 2 * Real.exp (-(a * q)) := by
    dsimp [a]
    simpa [mul_comm, mul_left_comm, mul_assoc] using squeeze_profile_eq c hc_pos q
  have hexp_le_one : Real.exp (-(a * q)) ≤ 1 := by
    have hnonneg_q : (0 : Real) ≤ q := by exact_mod_cast Nat.zero_le q
    have hneg : -(a * q) ≤ 0 := by nlinarith
    simpa using Real.exp_le_exp.mpr hneg
  calc
    |Real.log (C q)| ≤ 2 * d q / Real.sqrt (rho q) := hsq q hqs
    _ ≤ 2 * Real.exp (a * q) / Real.sqrt (c ^ q) := hbound
    _ = 2 * Real.exp (-(a * q)) := hdecay
    _ ≤ 2 := by nlinarith
    _ ≤ eps * (q : Real) := hlin q hqlin

end Omega.Zeta
