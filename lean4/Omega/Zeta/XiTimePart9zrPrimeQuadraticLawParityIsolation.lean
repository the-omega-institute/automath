import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zr-prime-quadratic-law-parity-isolation`. -/
theorem paper_xi_time_part9zr_prime_quadratic_law_parity_isolation
    (rhoUnit : ℕ → ℝ) (rhoParity lambda Aphi : ℝ) (hlambda : 0 < lambda)
    (hAphi : 0 < Aphi) (hParity : rhoParity < lambda)
    (hasymp : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Nat.Prime p → Odd p →
      |(p : ℝ) ^ 2 * (1 - rhoUnit p / lambda) - Aphi| < ε) :
    ∃ p0 : ℕ, ∀ p : ℕ, p0 ≤ p → Nat.Prime p → Odd p →
      rhoParity < rhoUnit p ∧ rhoUnit p < lambda := by
  let delta : ℝ := (lambda - rhoParity) / lambda
  have hdelta_pos : 0 < delta := by
    exact div_pos (sub_pos.mpr hParity) hlambda
  obtain ⟨K, hK⟩ := exists_nat_gt ((Aphi + 1) / delta)
  have heps_pos : 0 < min (1 : ℝ) (Aphi / 2) := by
    exact lt_min (by norm_num) (half_pos hAphi)
  obtain ⟨N, hN⟩ := hasymp (min (1 : ℝ) (Aphi / 2)) heps_pos
  refine ⟨max N (max K 1), ?_⟩
  intro p hp hpPrime hpOdd
  have hNp : N ≤ p := le_trans (Nat.le_max_left _ _) hp
  have hKp : K ≤ p := le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hp
  have hp1 : 1 ≤ p := le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hp
  have hp_pos_nat : 0 < p := by omega
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos_nat
  have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp_sq_pos : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos hp_pos
  let E : ℝ := (p : ℝ) ^ 2 * (1 - rhoUnit p / lambda)
  have hclose : |E - Aphi| < min (1 : ℝ) (Aphi / 2) := by
    simpa [E] using hN p hNp hpPrime hpOdd
  have hclose_half : |E - Aphi| < Aphi / 2 :=
    lt_of_lt_of_le hclose (min_le_right _ _)
  have hclose_one : |E - Aphi| < 1 :=
    lt_of_lt_of_le hclose (min_le_left _ _)
  have hE_pos : 0 < E := by
    have hlow := (abs_lt.mp hclose_half).1
    linarith
  have hE_lt_Aphi_add_one : E < Aphi + 1 := by
    have hhi := (abs_lt.mp hclose_one).2
    linarith
  have hone_minus_eq : 1 - rhoUnit p / lambda = E / ((p : ℝ) ^ 2) := by
    dsimp [E]
    field_simp [hp_sq_pos.ne']
  have hratio_lt_one : rhoUnit p / lambda < 1 := by
    have hpos : 0 < 1 - rhoUnit p / lambda := by
      rw [hone_minus_eq]
      exact div_pos hE_pos hp_sq_pos
    linarith
  have hupper : rhoUnit p < lambda := by
    have hmul := mul_lt_mul_of_pos_right hratio_lt_one hlambda
    have hcancel : rhoUnit p / lambda * lambda = rhoUnit p := by
      field_simp [hlambda.ne']
    linarith
  have hp_le_sq : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
    nlinarith
  have hKp_real : (K : ℝ) ≤ p := by exact_mod_cast hKp
  have hquot_lt_sq : (Aphi + 1) / delta < (p : ℝ) ^ 2 :=
    lt_of_lt_of_le (lt_of_lt_of_le hK hKp_real) hp_le_sq
  have hAphi_add_one_lt : Aphi + 1 < delta * ((p : ℝ) ^ 2) := by
    have hmul := (div_lt_iff₀ hdelta_pos).1 hquot_lt_sq
    nlinarith
  have hE_lt_delta_mul : E < delta * ((p : ℝ) ^ 2) := by
    linarith
  have hone_minus_lt_delta : 1 - rhoUnit p / lambda < delta := by
    rw [hone_minus_eq]
    exact (div_lt_iff₀ hp_sq_pos).2 (by nlinarith)
  have hdelta_eq : delta = 1 - rhoParity / lambda := by
    dsimp [delta]
    field_simp [hlambda.ne']
  have hratio_lower : rhoParity / lambda < rhoUnit p / lambda := by
    rw [hdelta_eq] at hone_minus_lt_delta
    linarith
  have hlower : rhoParity < rhoUnit p := by
    have hmul := mul_lt_mul_of_pos_right hratio_lower hlambda
    have hcancel_left : rhoParity / lambda * lambda = rhoParity := by
      field_simp [hlambda.ne']
    have hcancel_right : rhoUnit p / lambda * lambda = rhoUnit p := by
      field_simp [hlambda.ne']
    linarith
  exact ⟨hlower, hupper⟩

end Omega.Zeta
