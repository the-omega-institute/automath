import Mathlib.Tactic
import Omega.Folding.MomentRecurrence

/-! ### Window-6 q-moment spectrum and collision probability

Arithmetic certificates for the conclusion chapter:
q-moment triple from histogram {2:8, 3:4, 4:9}, collision probability reduction,
and related Wedderburn dimension identities. -/

namespace Omega.Conclusion

-- ══════════════════════════════════════════════════════════════
-- Phase R130: Window-6 q-moment spectrum triple
-- ══════════════════════════════════════════════════════════════

/-- Window-6 q-moment spectrum from histogram {2:8, 3:4, 4:9}.
    S_0=21, S_1=64, S_2=212.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_qmoment_triple :
    8 + 4 + 9 = 21 ∧
    8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
    8 * 4 + 4 * 9 + 9 * 16 = 212 := by omega

/-- S_2(6) = Σ d(w)² = Wedderburn dimension 212.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_S2_wedderburn :
    8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 := by omega

/-- Likelihood ratio monotonicity: sector weights shift toward large fibers.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_likelihood_shift :
    9 * 16 * 21 > 9 * 4 * 64 ∧ 9 * 4 * 21 > 9 * 1 * 64 := by omega

/-- The 4-fiber vs 2-fiber likelihood ratio grows strictly with q.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_lr_four_vs_two_strictMono :
    StrictMono (fun q : Nat => ((9 : ℚ) * (4 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) := by
  have hfun :
      (fun q : Nat => ((9 : ℚ) * (4 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) =
      fun q : Nat => ((9 : ℚ) / 8) * (2 : ℚ)^q := by
    funext q
    have hq : ((9 : ℚ) * (4 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q) =
        ((9 : ℚ) / 8) * (((4 : ℚ)^q) / ((2 : ℚ)^q)) := by
      field_simp [pow_ne_zero q (by norm_num : (2 : ℚ) ≠ 0)]
    rw [hq]
    congr 1
    calc
      ((4 : ℚ)^q) / ((2 : ℚ)^q) = ((4 : ℚ) / 2) ^ q := by rw [← div_pow]
      _ = (2 : ℚ)^q := by norm_num
  rw [hfun]
  intro a b hab
  have hpow : (2 : ℚ) ^ a < (2 : ℚ) ^ b := by
    exact pow_lt_pow_right₀ (by norm_num) hab
  have hconst : 0 < (9 : ℚ) / 8 := by norm_num
  exact mul_lt_mul_of_pos_left hpow hconst

/-- The 3-fiber vs 2-fiber likelihood ratio grows strictly with q.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_lr_three_vs_two_strictMono :
    StrictMono (fun q : Nat => ((4 : ℚ) * (3 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) := by
  have hfun :
      (fun q : Nat => ((4 : ℚ) * (3 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) =
      fun q : Nat => ((1 : ℚ) / 2) * ((3 : ℚ) / 2)^q := by
    funext q
    have hq : ((4 : ℚ) * (3 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q) =
        ((1 : ℚ) / 2) * (((3 : ℚ)^q) / ((2 : ℚ)^q)) := by
      field_simp [pow_ne_zero q (by norm_num : (2 : ℚ) ≠ 0)]
      ring
    rw [hq]
    congr 1
    rw [← div_pow]
  rw [hfun]
  intro a b hab
  have hpow : ((3 : ℚ) / 2) ^ a < ((3 : ℚ) / 2) ^ b := by
    exact pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < (3 : ℚ) / 2) hab
  have hconst : 0 < (1 : ℚ) / 2 := by norm_num
  exact mul_lt_mul_of_pos_left hpow hconst

/-- The 4-fiber vs 2-fiber likelihood ratio grows strictly with q.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_likelihood_ratio_42_strictMono :
    StrictMono (fun q : Nat => ((9 : ℚ) * (4 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) := by
  exact window6_lr_four_vs_two_strictMono

/-- The 3-fiber vs 2-fiber likelihood ratio grows strictly with q.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_likelihood_ratio_32_strictMono :
    StrictMono (fun q : Nat => ((4 : ℚ) * (3 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) := by
  exact window6_lr_three_vs_two_strictMono

-- ══════════════════════════════════════════════════════════════
-- Phase R130: Window-6 collision probability rational form
-- ══════════════════════════════════════════════════════════════

/-- Collision probability fraction: 212/4096 = 53/1024.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_prob_reduced :
    212 * 1024 = 53 * 4096 := by omega

/-- GCD reduction factor.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_gcd : Nat.gcd 212 4096 = 4 := by native_decide

/-- Microstate count squared: 64² = 4096.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_microstate_sq : 64 ^ 2 = 4096 := by omega

/-- Reduced fraction components.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_components :
    212 / 4 = 53 ∧ 4096 / 4 = 1024 := by omega

/-- Collision dimension exceeds 3× microstate count.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_exceeds_linear : 212 > 3 * 64 := by omega

/-- Paper: thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem paper_window6_collision_prob :
    212 * 1024 = 53 * 4096 := window6_collision_prob_reduced

-- ══════════════════════════════════════════════════════════════
-- Phase R136: Quadratic residues mod 21
-- ══════════════════════════════════════════════════════════════

/-- Decidable predicate: is a a nonzero quadratic residue mod 21? -/
def isNonzeroQR21 (a : Nat) : Bool :=
  a != 0 && (List.range 21).any (fun x => x * x % 21 == a)

/-- Number of nonzero quadratic residues in Z/21Z equals 7.
    prop:conclusion-window6-crt-euler-phi -/
theorem quadratic_residues_mod21 :
    ((Finset.range 21).filter (fun a => isNonzeroQR21 a)).card = 7 := by native_decide

/-- The nonzero QRs mod 21 are {1, 4, 7, 9, 15, 16, 18}.
    prop:conclusion-window6-crt-euler-phi -/
theorem quadratic_residues_mod21_explicit :
    (Finset.range 21).filter (fun a => isNonzeroQR21 a) = {1, 4, 7, 9, 15, 16, 18} := by
  native_decide

/-- Paper: prop:conclusion-window6-crt-euler-phi -/
theorem paper_quadratic_residues_mod21 :
    ((Finset.range 21).filter (fun a => isNonzeroQR21 a)).card = 7 :=
  quadratic_residues_mod21

-- ══════════════════════════════════════════════════════════════
-- Phase R138: Window-8 histogram consistency + higher moments
-- ══════════════════════════════════════════════════════════════

/-- Window-8 bin-fold histogram {3:21, 5:11, 6:23} consistency checks.
    thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem window8_histogram_consistency :
    21 + 11 + 23 = 55 ∧ 21 * 3 + 11 * 5 + 23 * 6 = 256 := by omega

/-- Higher moment sums from window-8 histogram.
    thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem window8_higher_moments :
    21 * 3 ^ 3 + 11 * 5 ^ 3 + 23 * 6 ^ 3 = 6910 ∧
    21 * 3 ^ 4 + 11 * 5 ^ 4 + 23 * 6 ^ 4 = 38384 ∧
    21 * 3 ^ 5 + 11 * 5 ^ 5 + 23 * 6 ^ 5 = 218326 := by omega

/-- Paper: thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem paper_window8_higher_moments :
    21 * 3 ^ 3 + 11 * 5 ^ 3 + 23 * 6 ^ 3 = 6910 ∧
    21 * 3 ^ 4 + 11 * 5 ^ 4 + 23 * 6 ^ 4 = 38384 ∧
    21 * 3 ^ 5 + 11 * 5 ^ 5 + 23 * 6 ^ 5 = 218326 :=
  window8_higher_moments

-- ══════════════════════════════════════════════════════════════
-- Phase R144: CRT idempotents mod 21
-- ══════════════════════════════════════════════════════════════

/-- Decidable idempotent predicate mod 21. -/
def isIdempotent21 (a : Nat) : Bool := a * a % 21 == a

/-- Number of idempotents in Z/21Z is exactly 4.
    prop:conclusion-window6-crt-euler-phi -/
theorem idempotent_count_mod21 :
    ((Finset.range 21).filter (fun a => isIdempotent21 a)).card = 4 := by native_decide

/-- The idempotents in Z/21Z are {0, 1, 7, 15}.
    prop:conclusion-window6-crt-euler-phi -/
theorem idempotent_set_mod21 :
    (Finset.range 21).filter (fun a => isIdempotent21 a) = {0, 1, 7, 15} := by native_decide

/-- Paper: prop:conclusion-window6-crt-euler-phi -/
theorem paper_idempotent_count_mod21 :
    ((Finset.range 21).filter (fun a => isIdempotent21 a)).card = 4 :=
  idempotent_count_mod21

-- ══════════════════════════════════════════════════════════════
-- Phase R160: Chi^2 numerator certificates
-- ══════════════════════════════════════════════════════════════

open Omega in
/-- Chi^2 numerator for Fold m=6,7,8: |X_m|·S_2(m) - 4^m.
    thm:conclusion-foldbin-groupoid-dimension-collision-chi2 -/
theorem paper_fold_chi2_certificates :
    (Fintype.card (X 6) * momentSum 2 6 - 4 ^ 6 = 524) ∧
    (Fintype.card (X 7) * momentSum 2 7 - 4 ^ 7 = 2112) ∧
    (Fintype.card (X 8) * momentSum 2 8 - 4 ^ 8 = 8824) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [X.card_eq_fib, momentSum_two_six]; native_decide
  · rw [X.card_eq_fib, momentSum_two_seven]; native_decide
  · rw [X.card_eq_fib, momentSum_two_eight_rec]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R166: Section ledger product formula
-- ══════════════════════════════════════════════════════════════

/-- The number of choice functions on fibers equals the product of fiber sizes.
    thm:conclusion-section-ledger-kl-identity -/
theorem section_count_eq_prod_fiber {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (F : α → β) :
    Fintype.card ((b : β) → {a : α // F a = b}) =
      ∏ b : β, (Finset.univ.filter (fun a => F a = b)).card := by
  rw [Fintype.card_pi]
  congr 1
  ext b
  exact Fintype.card_subtype (fun a => F a = b)

-- ══════════════════════════════════════════════════════════════
-- Phase R169: Log-sum inequality
-- ══════════════════════════════════════════════════════════════

/-- Log of product equals sum of logs for positive naturals.
    thm:conclusion-section-ledger-kl-identity -/
theorem log_prod_eq_sum_log {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    Real.log (∏ i, (d i : ℝ)) = ∑ i, Real.log (d i) := by
  apply Real.log_prod
  intro x _
  exact Nat.cast_pos.mpr (hd x) |>.ne'

/-- Log-sum inequality (AM-GM in log form): for positive reals summing to N,
    Σ log(a_i) ≤ n · log(N/n).
    thm:conclusion-section-ledger-kl-identity -/
theorem log_sum_le_of_sum_eq {n : ℕ} {N : ℝ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hn : 0 < n) (hsum : ∑ i, a i = N) (hN_pos : 0 < N) :
    ∑ i, Real.log (a i) ≤ n * Real.log (N / n) := by
  rw [← Real.log_prod (fun x _ => ne_of_gt (ha x))]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hprod_pos : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have hgm0 := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) a
    (fun _ _ => by positivity)
    (by simp [hn])
    (fun i _ => le_of_lt (ha i))
  have hgm : (∏ i, a i) ^ ((n : ℝ)⁻¹) ≤ N / n := by
    simpa [hsum, div_eq_mul_inv] using hgm0
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg hprod_pos.le _)
    hgm
    (show 0 ≤ (n : ℝ) from by positivity)
  have hprod : ∏ i, a i ≤ (N / n) ^ n := by
    have hleft0 : ((∏ i, a i) ^ ((n : ℝ)⁻¹)) ^ (n : ℝ) = (∏ i, a i) ^ (((n : ℝ)⁻¹) * n) := by
      rw [← Real.rpow_mul hprod_pos.le]
    have hleft : ((∏ i, a i) ^ ((n : ℝ)⁻¹)) ^ (n : ℝ) = ∏ i, a i := by
      rw [hleft0, inv_mul_cancel₀ (show (n : ℝ) ≠ 0 from by positivity), Real.rpow_one]
    have hright : (N / n) ^ (n : ℝ) = (N / n) ^ n := by rw [Real.rpow_natCast]
    rw [hleft, hright] at hpow
    exact hpow
  have hlog := Real.log_le_log hprod_pos hprod
  have hdiv_pos : 0 < N / n := by exact div_pos hN_pos hnR
  have hrw : Real.log ((N / n) ^ n) = n * Real.log (N / n) := by
    rw [← Real.rpow_natCast, Real.log_rpow hdiv_pos]
  simpa [hrw] using hlog

-- ══════════════════════════════════════════════════════════════
-- Phase R169: Window-10 histogram consistency
-- ══════════════════════════════════════════════════════════════

/-- Window-10 basic: |X_10|=144, 2^10=1024, S_1(10)=1024.
    thm:conclusion-window10-groupoid-collision-dimension-identity -/
theorem window10_basic_consistency :
    Fintype.card (X 10) = 144 ∧
    (2 : ℕ) ^ 10 = 1024 ∧
    momentSum 1 10 = 1024 := by
  refine ⟨?_, by norm_num, ?_⟩
  · rw [X.card_eq_fib]; native_decide
  · rw [momentSum_one]; norm_num

/-- Window-10 S_2 value: S_2(10) = 8320.
    thm:conclusion-window10-groupoid-collision-dimension-identity -/
theorem window10_S2 : momentSum 2 10 = 8320 := by
  rw [← cMomentSum_eq]; native_decide

end Omega.Conclusion
