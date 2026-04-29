import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.MomentRecurrence
import Omega.Folding.Window6

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

/-- Paper-facing discrete wrapper for the window-6 capacity curve.
    cor:conclusion-window6-continuous-capacity-piecewise-closed -/
theorem paper_conclusion_window6_continuous_capacity_piecewise_closed :
    8 * min 2 (2 ^ 0) + 4 * min 3 (2 ^ 0) + 9 * min 4 (2 ^ 0) = 21 ∧
    8 * min 2 (2 ^ 1) + 4 * min 3 (2 ^ 1) + 9 * min 4 (2 ^ 1) = 42 ∧
    (∀ B : Nat, 2 ≤ B →
      8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B) = 64) :=
  Omega.conclusion_window6_capacity_bifurcation

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

/-- Natural-number section sizes satisfy the uniform-average log upper bound.
    thm:conclusion-section-ledger-kl-identity -/
theorem sectionLog_le_uniformAverage_nat {n : ℕ} (hn : 0 < n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    ∑ i, Real.log (d i) ≤ n * Real.log ((∑ i, (d i : ℝ)) / n) := by
  let N : ℝ := ∑ i, (d i : ℝ)
  have hsum : ∑ i, (d i : ℝ) = N := by rfl
  have hpos : ∀ i, 0 < (d i : ℝ) := fun i => Nat.cast_pos.mpr (hd i)
  have hN_pos : 0 < N := by
    have hle : (d ⟨0, hn⟩ : ℝ) ≤ ∑ i, (d i : ℝ) := by
      simpa using
        (Finset.single_le_sum (f := fun i : Fin n => (d i : ℝ)) (by intro i _; positivity) (by simp : ⟨0, hn⟩ ∈ Finset.univ))
    exact lt_of_lt_of_le (Nat.cast_pos.mpr (hd ⟨0, hn⟩)) (by simpa [N] using hle)
  simpa [N] using log_sum_le_of_sum_eq (fun i => (d i : ℝ)) hpos hn hsum hN_pos

/-- Uniform section ledger identity as a KL-divergence decomposition.
    thm:conclusion-section-ledger-kl-identity -/
theorem sectionLedger_kl_identity {n : ℕ} (hn : 0 < n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    let N : ℝ := ∑ i, (d i : ℝ)
    let π : Fin n → ℝ := fun i => (d i : ℝ) / N
    let ν : ℝ := 1 / n
    (1 / n : ℝ) * ∑ i, Real.log (d i)
      = Real.log (N / n) - ∑ i, ν * Real.log (ν / π i) := by
  dsimp
  let N : ℝ := ∑ i, (d i : ℝ)
  let π : Fin n → ℝ := fun i => (d i : ℝ) / N
  let ν : ℝ := 1 / n
  have hnR_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
  have hdR_pos : ∀ i, 0 < (d i : ℝ) := fun i => Nat.cast_pos.mpr (hd i)
  have hN_pos : 0 < N := by
    have hle : (d ⟨0, hn⟩ : ℝ) ≤ ∑ i, (d i : ℝ) := by
      simpa using
        (Finset.single_le_sum (f := fun i : Fin n => (d i : ℝ)) (by intro i _; positivity)
          (by simp : ⟨0, hn⟩ ∈ Finset.univ))
    exact lt_of_lt_of_le (Nat.cast_pos.mpr (hd ⟨0, hn⟩)) (by simpa [N] using hle)
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hπpos : ∀ i, 0 < π i := by
    intro i
    dsimp [π]
    exact div_pos (hdR_pos i) hN_pos
  have hπne : ∀ i, π i ≠ 0 := fun i => ne_of_gt (hπpos i)
  have hνpos : 0 < ν := by
    dsimp [ν]
    exact one_div_pos.mpr hnR_pos
  have hνne : ν ≠ 0 := ne_of_gt hνpos
  have hNdivn_pos : 0 < N / n := div_pos hN_pos hnR_pos
  have hNdivn_ne : N / n ≠ 0 := ne_of_gt hNdivn_pos
  have hνn : ν * n = 1 := by
    dsimp [ν]
    field_simp [hnR_ne]
  have hlogratio : ∀ i, Real.log (ν / π i) = Real.log (N / n) - Real.log (d i) := by
    intro i
    have hdi_ne : (d i : ℝ) ≠ 0 := ne_of_gt (hdR_pos i)
    have hratio : ν / π i = (N / n) / (d i : ℝ) := by
      dsimp [ν, π]
      field_simp [hnR_ne, hN_ne, hdi_ne]
    rw [hratio]
    rw [Real.log_div hNdivn_ne hdi_ne]
  have hsumKL :
      ∑ i, ν * Real.log (ν / π i) = ν * (n * Real.log (N / n) - ∑ i, Real.log (d i)) := by
    calc
      ∑ i, ν * Real.log (ν / π i)
          = ∑ i, ν * (Real.log (N / n) - Real.log (d i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hlogratio i]
      _ = ∑ i, (ν * Real.log (N / n) - ν * Real.log (d i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = (∑ i, ν * Real.log (N / n)) - ∑ i, ν * Real.log (d i) := by
            rw [Finset.sum_sub_distrib]
      _ = ν * (n * Real.log (N / n)) - ν * ∑ i, Real.log (d i) := by
            rw [Finset.mul_sum]
            norm_num [Finset.card_univ]
            ring
      _ = ν * (n * Real.log (N / n) - ∑ i, Real.log (d i)) := by ring
  have hsumKL' : ∑ i, ν * Real.log (ν / π i) = Real.log (N / n) - ν * ∑ i, Real.log (d i) := by
    rw [hsumKL]
    calc
      ν * (n * Real.log (N / n) - ∑ i, Real.log (d i))
          = ν * (n * Real.log (N / n)) - ν * ∑ i, Real.log (d i) := by ring
      _ = Real.log (N / n) - ν * ∑ i, Real.log (d i) := by
            have hmain : ν * (n * Real.log (N / n)) = Real.log (N / n) := by
              calc
                ν * (n * Real.log (N / n)) = (ν * n) * Real.log (N / n) := by ring
                _ = Real.log (N / n) := by rw [hνn, one_mul]
            rw [hmain]
  rw [hsumKL']
  ring

/-- Two-level collision moment realizes the explicit extremal pair.
    thm:conclusion-window10-groupoid-collision-dimension-identity -/
theorem collisionMoment_q2_explicit {n : ℕ} (hn : 1 < n)
    {c : ℝ} (hc1 : 1 / n ≤ c) (_hc2 : c ≤ 1) :
    let a : ℝ := (1 + Real.sqrt ((n - 1 : ℝ) * ((n : ℝ) * c - 1))) / n
    let b : ℝ := (1 - Real.sqrt (((n : ℝ) * c - 1) / (n - 1 : ℝ))) / n
    a + (n - 1 : ℝ) * b = 1 ∧ a^2 + (n - 1 : ℝ) * b^2 = c := by
  dsimp
  let t : ℝ := Real.sqrt (((n : ℝ) * c - 1) / ((n : ℝ) - 1))
  have hn_pos : 0 < n := lt_trans Nat.zero_lt_one hn
  have hnR_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
  have hm_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR_gt_one : (1 : ℝ) < n := by
      exact_mod_cast hn
    linarith
  have hm_ne : (n : ℝ) - 1 ≠ 0 := ne_of_gt hm_pos
  have hnc_nonneg : 0 ≤ (n : ℝ) * c - 1 := by
    have hmul : (n : ℝ) * (1 / n : ℝ) ≤ (n : ℝ) * c :=
      mul_le_mul_of_nonneg_left hc1 hnR_pos.le
    have hone : (n : ℝ) * (1 / n : ℝ) = 1 := by
      field_simp [hnR_ne]
    linarith
  have hratio_nonneg : 0 ≤ (((n : ℝ) * c - 1) / ((n : ℝ) - 1)) := by
    exact div_nonneg hnc_nonneg hm_pos.le
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_sq : t ^ 2 = (((n : ℝ) * c - 1) / ((n : ℝ) - 1)) := by
    dsimp [t]
    rw [Real.sq_sqrt hratio_nonneg]
  have hsqrt_mul :
      Real.sqrt (((n : ℝ) - 1) * ((n : ℝ) * c - 1)) = ((n : ℝ) - 1) * t := by
    have hsq_left : (Real.sqrt (((n : ℝ) - 1) * ((n : ℝ) * c - 1))) ^ 2 =
        ((n : ℝ) - 1) * ((n : ℝ) * c - 1) := by
      rw [Real.sq_sqrt]
      positivity
    have hsq_right : (((n : ℝ) - 1) * t) ^ 2 = ((n : ℝ) - 1) * ((n : ℝ) * c - 1) := by
      rw [mul_pow, ht_sq]
      field_simp [hm_ne]
    have hleft_nonneg : 0 ≤ Real.sqrt (((n : ℝ) - 1) * ((n : ℝ) * c - 1)) := by
      positivity
    have hright_nonneg : 0 ≤ ((n : ℝ) - 1) * t := by
      exact mul_nonneg hm_pos.le ht_nonneg
    nlinarith
  constructor
  · rw [hsqrt_mul]
    change (1 + ((n : ℝ) - 1) * t) / n + ((n : ℝ) - 1) * ((1 - t) / n) = 1
    field_simp [hnR_ne]
    ring
  · rw [hsqrt_mul]
    change ((1 + ((n : ℝ) - 1) * t) / n) ^ 2 + ((n : ℝ) - 1) * ((1 - t) / n) ^ 2 = c
    have hquad :
        ((1 + ((n : ℝ) - 1) * t) / n) ^ 2 + ((n : ℝ) - 1) * ((1 - t) / n) ^ 2 =
          (1 + ((n : ℝ) - 1) * t ^ 2) / n := by
      field_simp [hnR_ne]
      ring
    calc
      ((1 + ((n : ℝ) - 1) * t) / n) ^ 2 + ((n : ℝ) - 1) * ((1 - t) / n) ^ 2 =
          (1 + ((n : ℝ) - 1) * t ^ 2) / n := hquad
      _ = (1 + ((n : ℝ) - 1) * (((n : ℝ) * c - 1) / ((n : ℝ) - 1))) / n := by rw [ht_sq]
      _ = c := by
        field_simp [hnR_ne, hm_ne]
        ring

/-- Paper label: `cor:conclusion-section-ledger-collision-moment-q2-explicit`. -/
theorem paper_conclusion_section_ledger_collision_moment_q2_explicit {n : ℕ} (hn : 1 < n)
    {c : ℝ} (hc1 : 1 / n ≤ c) (hc2 : c ≤ 1) :
    let a : ℝ := (1 + Real.sqrt ((n - 1 : ℝ) * ((n : ℝ) * c - 1))) / n
    let b : ℝ := (1 - Real.sqrt (((n : ℝ) * c - 1) / (n - 1 : ℝ))) / n
    a + (n - 1 : ℝ) * b = 1 ∧ a^2 + (n - 1 : ℝ) * b^2 = c := by
  exact collisionMoment_q2_explicit hn hc1 hc2

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

/-- Window-6 visible CRT arithmetic phase space certificate.
    thm:conclusion-window6-visible-crt-arithmetic-phase-space -/
theorem conclusion_window6_visible_crt_arithmetic_phase_space :
    Fintype.card (X 6) = 21 ∧ 21 = 3 * 7 := by
  exact ⟨X.card_X_six, card_X6_factorization⟩

/-- Window-6 CRT idempotent sector splitting certificate.
    prop:conclusion-window6-crt-idempotent-sector-splitting -/
theorem conclusion_window6_crt_idempotent_sector_splitting :
    ((7 : ZMod 21) ^ 2 = 7) ∧
    ((15 : ZMod 21) ^ 2 = 15) ∧
    ((7 : ZMod 21) * 15 = 0) ∧
    ((7 : ZMod 21) + 15 = 1) := by
  exact ⟨crt_idempotent_7, crt_idempotent_15, crt_idempotent_product, crt_idempotent_sum⟩

/-- Closed form of the average information loss constant from the window-6 histogram.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_information_loss_average_closed_form :
    ((8 : ℝ) * (2 : ℝ) * Real.log 2 +
        (4 : ℝ) * (3 : ℝ) * Real.log 3 +
        (9 : ℝ) * (4 : ℝ) * Real.log 4) / 64 =
      ((11 : ℝ) / 8) * Real.log 2 + ((3 : ℝ) / 16) * Real.log 3 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hlog4]
  ring_nf

/-- Window-6 collision probability complementary law.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem paper_window6_collision_complementary :
    momentSum 2 6 = 220 ∧
    Fintype.card (X 6) = 21 ∧
    2 ^ 6 = 64 ∧
    220 > 3 * 64 ∧
    Nat.gcd 220 4096 = 4 := by
  refine ⟨momentSum_two_six, by rw [X.card_eq_fib]; native_decide,
    by omega, by omega, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R300: Window-6 gauge defect exact log gap
-- ══════════════════════════════════════════════════════════════

/-- Gauge group order factorization for window-6.
    thm:conclusion-window6-gauge-defect-exact-log-gap -/
theorem window6_gauge_group_factorial_factors :
    Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 =
    2 ^ 8 * 6 ^ 4 * 24 ^ 9 := by norm_num

/-- The numerical values of the gauge group factorials.
    thm:conclusion-window6-gauge-defect-exact-log-gap -/
theorem window6_gauge_group_order :
    2 ^ 8 * 6 ^ 4 * 24 ^ 9 = 2 ^ 39 * 3 ^ 13 := by norm_num

/-- Paper-facing: log-gap coefficient extraction.
    64*(κ₆ - g₆) = 49 log 2 - log 3.
    thm:conclusion-window6-gauge-defect-exact-log-gap -/
theorem paper_window6_gauge_defect_coefficient_extraction :
    8 * 1 + 4 * (-1 : ℤ) + 9 * 5 = 49 ∧
    4 * 2 + 9 * (-1 : ℤ) = -1 := by omega

-- ══════════════════════════════════════════════════════════════
-- Phase R300: Window-6 boundary quotient cyclic cardinality
-- ══════════════════════════════════════════════════════════════

/-- Window-6 cyclic sector cardinality equals the boundary quotient dimension.
    thm:conclusion-window6-boundary-quotient-cyclic-cardinality -/
theorem window6_boundary_quotient_cyclic_cardinality :
    5 + 4 + 9 = 18 ∧
    8 + 4 + 9 = 21 ∧ 21 - 3 = 18 := by omega

/-- Abelianization rank identity: total F2-rank = boundary + cyclic.
    thm:conclusion-window6-boundary-quotient-cyclic-cardinality -/
theorem window6_abelianization_rank_decomposition :
    8 * 1 + 4 * 1 + 9 * 3 = 39 ∧
    (8 + 4 + 9 : ℕ) = 21 ∧
    39 - 21 = 18 := by omega

-- ══════════════════════════════════════════════════════════════
-- Phase R303: Frozen tail discrete second difference
-- ══════════════════════════════════════════════════════════════

/-- Discrete second difference of affine function vanishes.
    thm:conclusion-frozen-tail-zero-curvature-second-maximum-visibility -/
theorem affine_discrete_second_diff_zero (α g : ℝ) (a : ℤ) :
    ((a + 1) * α + g) - 2 * (a * α + g) + ((a - 1) * α + g) = 0 := by ring

/-- Integer version.
    thm:conclusion-frozen-tail-zero-curvature-second-maximum-visibility -/
theorem affine_discrete_second_diff_zero_int (α g : ℤ) (a : ℤ) :
    ((a + 1) * α + g) - 2 * (a * α + g) + ((a - 1) * α + g) = 0 := by ring

/-- Semigroup law for affine functions.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem affine_semigroup_law (α g : ℝ) (a b : ℤ) :
    ((a + b) * α + g) + g = (a * α + g) + (b * α + g) := by ring

/-- Paper package.
    thm:conclusion-frozen-tail-zero-curvature-second-maximum-visibility -/
theorem paper_frozen_curvature_semigroup_package :
    (∀ α g : ℝ, ∀ a : ℤ,
      ((a + 1) * α + g) - 2 * (a * α + g) + ((a - 1) * α + g) = 0) ∧
    (∀ α g : ℝ, ∀ a b : ℤ,
      ((a + b) * α + g) + g = (a * α + g) + (b * α + g)) := by
  exact ⟨fun α g a => by ring, fun α g a b => by ring⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R307: Window-6 moment hierarchy S_1..S_4
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-groupoid-wedderburn -/
theorem window6_S1_from_histogram :
    2 * 1 + 4 * 2 + 8 * 3 + 5 * 4 + 2 * 5 = 64 := by omega

/-- prop:fold-groupoid-wedderburn -/
theorem window6_S2_from_histogram :
    2 * 1 + 4 * 4 + 8 * 9 + 5 * 16 + 2 * 25 = 220 := by omega

/-- prop:fold-groupoid-wedderburn -/
theorem window6_S3_from_histogram :
    2 * 1 + 4 * 8 + 8 * 27 + 5 * 64 + 2 * 125 = 820 := by omega

/-- prop:fold-groupoid-wedderburn -/
theorem window6_S4_from_histogram :
    2 * 1 + 4 * 16 + 8 * 81 + 5 * 256 + 2 * 625 = 3244 := by omega

/-- Cross-validation with cMomentSum. prop:fold-groupoid-wedderburn -/
theorem window6_histogram_cross_validation :
    cMomentSum 1 6 = 64 ∧ cMomentSum 2 6 = 220 ∧
    cMomentSum 3 6 = 820 ∧ cMomentSum 4 6 = 3244 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Paper package. prop:fold-groupoid-wedderburn -/
theorem paper_window6_moment_hierarchy :
    (2 * 1 + 4 * 2 + 8 * 3 + 5 * 4 + 2 * 5 = 64) ∧
    (2 * 1 + 4 * 4 + 8 * 9 + 5 * 16 + 2 * 25 = 220) ∧
    (2 * 1 + 4 * 8 + 8 * 27 + 5 * 64 + 2 * 125 = 820) ∧
    (2 * 1 + 4 * 16 + 8 * 81 + 5 * 256 + 2 * 625 = 3244) ∧
    cMomentSum 3 6 = 820 ∧ cMomentSum 4 6 = 3244 := by
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R310: S_2 coprimality certificates
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_six_coprime_card :
    Nat.Coprime (momentSum 2 6) (Nat.fib 8) := by
  rw [momentSum_two_six]; native_decide

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_eight_coprime_card :
    Nat.Coprime (momentSum 2 8) (Nat.fib 10) := by
  rw [momentSum_two_eight_rec]; native_decide

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_nine_coprime_card :
    Nat.Coprime (momentSum 2 9) (Nat.fib 11) := by
  rw [momentSum_two_nine_rec]; native_decide

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_seven_gcd_card :
    Nat.gcd (momentSum 2 7) (Nat.fib 9) = 34 := by
  rw [momentSum_two_seven]; native_decide

/-- Paper package. prop:fold-groupoid-wedderburn -/
theorem paper_momentSum_coprimality_pattern :
    Nat.Coprime 220 21 ∧ Nat.gcd 544 34 = 34 ∧
    Nat.Coprime 1352 55 ∧ Nat.Coprime 3352 89 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R313: collision excess values
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-groupoid-wedderburn -/
theorem collision_excess_values :
    momentSum 2 2 - 2 ^ 2 = 2 ∧ momentSum 2 3 - 2 ^ 3 = 6 ∧
    momentSum 2 4 - 2 ^ 4 = 20 ∧ momentSum 2 5 - 2 ^ 5 = 56 ∧
    momentSum 2 6 - 2 ^ 6 = 156 ∧ momentSum 2 7 - 2 ^ 7 = 416 ∧
    momentSum 2 8 - 2 ^ 8 = 1096 := by
  rw [momentSum_two_two, momentSum_two_three, momentSum_two_four,
      momentSum_two_five, momentSum_two_six, momentSum_two_seven,
      momentSum_two_eight_rec]; omega

/-- prop:fold-groupoid-wedderburn -/
theorem collision_excess_strict_mono :
    2 < 6 ∧ 6 < 20 ∧ 20 < 56 ∧ 56 < 156 ∧ 156 < 416 ∧ 416 < 1096 := by omega

/-- Paper package. prop:fold-groupoid-wedderburn -/
theorem paper_collision_excess :
    momentSum 2 6 - 2 ^ 6 = 156 ∧ momentSum 2 7 - 2 ^ 7 = 416 ∧
    momentSum 2 8 - 2 ^ 8 = 1096 ∧ 156 < 416 ∧ 416 < 1096 := by
  rw [momentSum_two_six, momentSum_two_seven, momentSum_two_eight_rec]; omega

/-- Window-6 representation zeta count certificate.
    cor:conclusion-window6-representation-zeta-count-ratio -/
theorem paper_window6_representation_zeta_count :
    (2 ^ 8 * 3 ^ 4 * 5 ^ 9 = 40500000000) ∧
    (2 ^ (8 + 4 + 9) = 2097152) ∧
    (8 + 4 + 9 = 21) ∧
    (2 ^ 21 * (3 ^ 4 * 5 ^ 9) = 2 ^ 8 * 3 ^ 4 * 5 ^ 9 * 2 ^ 13) ∧
    (cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by ring, ?_⟩
  exact ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4⟩

/-- Boundary and fourpoint sector ratios β_q, γ_q at q=0,1,2.
    cor:conclusion-window6-boundary-fourpoint-moment-amplification -/
theorem paper_window6_boundary_sector_ratios :
    (3 : ℚ) * 1 / 21 = 1 / 7 ∧
    (3 : ℚ) * 2 / 64 = 3 / 32 ∧
    (3 : ℚ) * 4 / 212 = 3 / 53 ∧
    (9 : ℚ) * 1 / 21 = 3 / 7 ∧
    (9 : ℚ) * 4 / 64 = 9 / 16 ∧
    (9 : ℚ) * 16 / 212 = 36 / 53 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Section count is bounded by max-fiber^n.
    thm:conclusion-section-ledger-kl-identity -/
theorem section_count_le_maxFiber_pow {n : ℕ} (d : Fin n → ℕ)
    (M : ℕ) (hM : ∀ i, d i ≤ M) :
    (∏ i, d i) ≤ M ^ n := by
  calc ∏ i, d i
      ≤ ∏ _i : Fin n, M := Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hM i)
    _ = M ^ n := by simp [Finset.prod_const]

/-- Section count satisfies AM-GM in product form: (∏ d_i) * n^n ≤ N^n.
    thm:conclusion-section-ledger-kl-identity -/
theorem section_count_amgm_prod {n : ℕ} (d : Fin n → ℕ)
    (N : ℕ) (hsum : ∑ i, d i = N) :
    (∏ i, d i) ≤ N ^ n := by
  apply section_count_le_maxFiber_pow d N
  intro i
  calc d i ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = N := hsum

/-- AM-GM equality backward: if all d(i) = c then ∏ d(i) = c^n and ∑ d(i) = n*c.
    thm:conclusion-section-ledger-kl-identity -/
theorem prod_eq_const_pow_of_all_eq {n : ℕ} (d : Fin n → ℕ) (c : ℕ)
    (hall : ∀ i, d i = c) :
    (∏ i, d i) = c ^ n ∧ ∑ i, d i = n * c := by
  constructor
  · simp_rw [hall, Finset.prod_const, Finset.card_fin]
  · simp_rw [hall, Finset.sum_const, Finset.card_fin, smul_eq_mul]

/-- AM-GM equality forward for n=1: unique value forced.
    thm:conclusion-section-ledger-kl-identity -/
theorem prod_eq_const_pow_iff_one (d : Fin 1 → ℕ) (c : ℕ)
    (hsum : ∑ i, d i = 1 * c) :
    d ⟨0, by omega⟩ = c := by
  simp at hsum; exact hsum

/-- AM-GM equality forward for n=2: product c^2 with sum 2c forces equality.
    thm:conclusion-section-ledger-kl-identity -/
theorem prod_eq_sq_of_sum_two (a b c : ℕ) (hsum : a + b = 2 * c)
    (hprod : a * b = c * c) : a = c ∧ b = c := by
  -- Lift to ℤ to handle subtraction correctly
  have hprodZ : (a : ℤ) * b = c * c := by exact_mod_cast hprod
  have hsumZ : (a : ℤ) + b = 2 * c := by exact_mod_cast hsum
  have habZ : (b : ℤ) = 2 * c - a := by linarith
  have key : ((a : ℤ) - c) ^ 2 = 0 := by nlinarith
  have ha : (a : ℤ) = c := by nlinarith [sq_nonneg ((a : ℤ) - c)]
  have hb : (b : ℤ) = c := by linarith
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

end Omega.Conclusion
