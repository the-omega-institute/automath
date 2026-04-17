import Mathlib.Data.Int.ModEq
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- If a residue readout comes with a reconstruction procedure that is exact on the bounded
interval `[-B, B]`, then equality and order on that interval can be decided by reconstructing from
the residue and comparing in `ℤ`. The inequality `P > 2B` is kept as the paper's CRT-budget
certificate for the existence of such a reconstruction. -/
theorem paper_pom_order_spatialization
    (B P : ℕ) (reconstruct : ℤ → ℤ) (_hP : P > 2 * B)
    (hrec : ∀ {x : ℤ}, |x| ≤ B → reconstruct (x % P) = x)
    {x y : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    ((x % P : ℤ) = y % P ↔ x = y) ∧
      (reconstruct (x % P) ≤ reconstruct (y % P) ↔ x ≤ y) := by
  constructor
  · constructor
    · intro hmod
      have hx' : reconstruct (x % P) = x := hrec hx
      have hy' : reconstruct (y % P) = y := hrec hy
      rw [← hx', hmod, hy']
    · intro hxy
      simp [hxy]
  · have hx' : reconstruct (x % P) = x := hrec hx
    have hy' : reconstruct (y % P) = y := hrec hy
    simp [hx', hy']

/-- Paper: `cor:pom-order-mixing`.
    A logarithmic rearrangement of the exponential decay estimate. -/
theorem paper_pom_order_mixing {lambda1 Lambda epsilon : Real} {n : Nat} (heps : 0 < epsilon)
    (hgap : 0 < Lambda ∧ Lambda < lambda1) (herr : (Lambda / lambda1) ^ n <= epsilon) :
    Real.log (1 / epsilon) / Real.log (lambda1 / Lambda) <= n := by
  rcases hgap with ⟨hLambda_pos, hLambda_lt_lambda1⟩
  have hlambda1_pos : 0 < lambda1 := lt_trans hLambda_pos hLambda_lt_lambda1
  have hratio_pos : 0 < Lambda / lambda1 := div_pos hLambda_pos hlambda1_pos
  have hratio_lt_one : Lambda / lambda1 < 1 := by
    have hlt : Lambda / lambda1 < lambda1 / lambda1 := by
      exact div_lt_div_of_pos_right hLambda_lt_lambda1 hlambda1_pos
    simpa [hlambda1_pos.ne'] using hlt
  have hinv_ratio_gt_one : 1 < lambda1 / Lambda := by
    have hlt : Lambda / Lambda < lambda1 / Lambda := by
      exact div_lt_div_of_pos_right hLambda_lt_lambda1 hLambda_pos
    simpa [hLambda_pos.ne'] using hlt
  have hden_pos : 0 < Real.log (lambda1 / Lambda) := Real.log_pos hinv_ratio_gt_one
  by_cases heps_le_one : epsilon ≤ 1
  · have hpow_pos : 0 < (Lambda / lambda1) ^ n := pow_pos hratio_pos _
    have hlog_le : Real.log ((Lambda / lambda1) ^ n) ≤ Real.log epsilon :=
      Real.log_le_log hpow_pos herr
    have hlog_ratio :
        Real.log (lambda1 / Lambda) = -Real.log (Lambda / lambda1) := by
      have hinv : lambda1 / Lambda = (Lambda / lambda1)⁻¹ := by
        field_simp [hLambda_pos.ne', hlambda1_pos.ne']
      rw [hinv, Real.log_inv]
    have hlog_eps : Real.log (1 / epsilon) = -Real.log epsilon := by
      rw [one_div, Real.log_inv]
    rw [div_le_iff₀ hden_pos]
    rw [Real.log_pow] at hlog_le
    rw [hlog_eps, hlog_ratio]
    nlinarith
  · have heps_gt_one : 1 < epsilon := lt_of_not_ge heps_le_one
    have hinv_eps_pos : 0 < 1 / epsilon := one_div_pos.mpr heps
    have hinv_eps_le_one : 1 / epsilon ≤ 1 := by
      rw [div_le_iff₀ heps]
      simpa [one_mul] using heps_gt_one.le
    have hnum_nonpos : Real.log (1 / epsilon) ≤ 0 := by
      exact Real.log_nonpos hinv_eps_pos.le hinv_eps_le_one
    have hdiv_nonpos : Real.log (1 / epsilon) / Real.log (lambda1 / Lambda) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_pos.le
    have hn_nonneg : (0 : Real) ≤ n := by exact_mod_cast Nat.zero_le n
    linarith

end Omega.POM
