import Mathlib.Tactic

/-! ### Relative error threshold sharpness

The kappa function κ(ε) = (1+ε)/(1-ε) characterizes the relative error threshold
for spectral gap amplification. -/

namespace Omega.SPG

noncomputable def kappa (ε : ℝ) : ℝ := (1 + ε) / (1 - ε)

/-- When ε ≥ (p-1)/(p+1), κ(ε) ≥ p.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_ge_of_eps_ge {p ε : ℝ} (hp : 1 < p) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (heps : (p - 1) / (p + 1) ≤ ε) :
    p ≤ kappa ε := by
  unfold kappa
  rw [le_div_iff₀ (by linarith)]
  have hp1 : 0 < p + 1 := by linarith
  have := div_le_iff₀ hp1 |>.mp heps
  nlinarith

/-- Converse: κ(ε) < p implies ε < (p-1)/(p+1).
    prop:spg-relative-error-threshold-sharpness -/
theorem eps_lt_of_kappa_lt {p ε : ℝ} (hp : 1 < p) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hkappa : kappa ε < p) :
    ε < (p - 1) / (p + 1) := by
  unfold kappa at hkappa
  have h1ε : 0 < 1 - ε := by linarith
  rw [div_lt_iff₀ h1ε] at hkappa
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p + 1)]
  nlinarith

/-- Exact threshold criterion for `κ(ε) < p`.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_lt_iff_eps_lt {p ε : ℝ}
    (hp : 1 < p) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    kappa ε < p ↔ ε < (p - 1) / (p + 1) := by
  constructor
  · exact eps_lt_of_kappa_lt hp hε_pos hε_lt
  · intro hε
    unfold kappa
    have h1ε : 0 < 1 - ε := by linarith
    have hp1 : 0 < p + 1 := by linarith
    rw [div_lt_iff₀ h1ε]
    have hε' := (lt_div_iff₀ hp1).mp hε
    nlinarith

/-- The kappa function is strictly monotone on (0, 1).
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_strict_mono_on {a b : ℝ} (_ha : 0 < a) (_ha1 : a < 1) (_hb : 0 < b)
    (hb1 : b < 1) (hab : a < b) :
    kappa a < kappa b := by
  unfold kappa
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1b : (0 : ℝ) < 1 - b := by linarith
  rw [div_lt_div_iff₀ h1a h1b]
  nlinarith

/-- The kappa function is injective on (0, 1).
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_injective_on {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (heq : kappa a = kappa b) : a = b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact absurd heq (ne_of_lt (kappa_strict_mono_on ha ha1 hb hb1 hab))
  · rfl
  · exact absurd heq (ne_of_gt (kappa_strict_mono_on hb hb1 ha ha1 hba))

-- ══════════════════════════════════════════════════════════════
-- Phase R251: kappa inverse and concrete values
-- ══════════════════════════════════════════════════════════════

/-- Inverse of the kappa function: kappaInv(p) = (p-1)/(p+1).
    prop:spg-relative-error-threshold-sharpness -/
noncomputable def kappaInv (p : ℝ) : ℝ := (p - 1) / (p + 1)

/-- kappa ∘ kappaInv = id on (1, ∞).
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_kappaInv {p : ℝ} (hp : 1 < p) :
    kappa (kappaInv p) = p := by
  unfold kappa kappaInv
  have hp1 : p + 1 ≠ 0 := by linarith
  have h : 1 - (p - 1) / (p + 1) ≠ 0 := by
    have : 0 < 1 - (p - 1) / (p + 1) := by
      rw [sub_pos, div_lt_one (by linarith : (0 : ℝ) < p + 1)]
      linarith
    linarith
  field_simp
  ring

/-- kappaInv ∘ kappa = id on (0, 1).
    prop:spg-relative-error-threshold-sharpness -/
theorem kappaInv_kappa {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    kappaInv (kappa ε) = ε := by
  unfold kappa kappaInv
  have h1 : (1 : ℝ) - ε ≠ 0 := by linarith
  have h2 : (1 + ε) / (1 - ε) + 1 ≠ 0 := by
    have : 0 < (1 + ε) / (1 - ε) := div_pos (by linarith) (by linarith)
    linarith
  field_simp
  ring

/-- kappa(1/2) = 3.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_half : kappa (1 / 2 : ℝ) = 3 := by
  unfold kappa; norm_num

-- ══════════════════════════════════════════════════════════════
-- Phase R289: kappa/kappaInv basic properties
-- ══════════════════════════════════════════════════════════════

/-- kappa(0) = 1. prop:spg-relative-error-threshold-sharpness -/
theorem kappa_zero : kappa 0 = 1 := by unfold kappa; norm_num

/-- kappa(ε) > 1 for 0 < ε < 1. prop:spg-relative-error-threshold-sharpness -/
theorem kappa_gt_one {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) : 1 < kappa ε := by
  unfold kappa
  rw [one_lt_div (by linarith)]
  linarith

/-- kappa(1/3) = 2. prop:spg-relative-error-threshold-sharpness -/
theorem kappa_third : kappa (1 / 3 : ℝ) = 2 := by unfold kappa; norm_num

/-- kappaInv(p) > 0 for p > 1. prop:spg-relative-error-threshold-sharpness -/
theorem kappaInv_pos {p : ℝ} (hp : 1 < p) : 0 < kappaInv p := by
  unfold kappaInv; apply div_pos <;> linarith

/-- kappaInv(p) < 1 for p > 1. prop:spg-relative-error-threshold-sharpness -/
theorem kappaInv_lt_one {p : ℝ} (hp : 1 < p) : kappaInv p < 1 := by
  unfold kappaInv
  rw [div_lt_one (by linarith : (0 : ℝ) < p + 1)]
  linarith

/-- Special values package for kappa and kappaInv.
    prop:spg-relative-error-threshold-sharpness -/
theorem paper_kappa_special_values_package :
    kappa 0 = 1 ∧
    kappa (1 / 3 : ℝ) = 2 ∧
    kappa (1 / 2 : ℝ) = 3 ∧
    kappaInv 2 = (1 / 3 : ℝ) ∧
    kappaInv 3 = (1 / 2 : ℝ) := by
  refine ⟨kappa_zero, kappa_third, kappa_half, ?_, ?_⟩ <;>
    unfold kappaInv <;> norm_num

/-- Relative error threshold sharpness.
    prop:spg-relative-error-threshold-sharpness -/
theorem paper_kappa_threshold_criterion :
    (∀ p ε : ℝ, 1 < p → 0 < ε → ε < 1 →
      (kappa ε < p ↔ ε < (p - 1) / (p + 1))) ∧
    (∀ p ε : ℝ, 1 < p → 0 < ε → ε < 1 →
      (p - 1) / (p + 1) ≤ ε → p ≤ kappa ε) :=
  ⟨fun _ _ hp hε hε1 => kappa_lt_iff_eps_lt hp hε hε1,
   fun _ _ hp hε hε1 heps => kappa_ge_of_eps_ge hp hε hε1 heps⟩

/-- Kappa-Fibonacci crosspoint verification.
    prop:spg-relative-error-threshold-sharpness -/
theorem paper_kappa_fibonacci_crosspoints :
    (Nat.fib 5 - 1) * 3 = (Nat.fib 5 + 1) * 2 ∧
    (Nat.fib 6 - 1) = 7 ∧ (Nat.fib 6 + 1) = 9 ∧
    (Nat.fib 7 - 1) * 7 = (Nat.fib 7 + 1) * 6 ∧
    (Nat.fib 8 - 1) * 11 = (Nat.fib 8 + 1) * 10 := by
  native_decide

/-- kappa(1/4) = 5/3. prop:spg-relative-error-threshold-sharpness -/
theorem kappa_quarter : kappa (1 / 4 : ℝ) = 5 / 3 := by unfold kappa; norm_num

/-- kappa(1/5) = 3/2. prop:spg-relative-error-threshold-sharpness -/
theorem kappa_fifth : kappa (1 / 5 : ℝ) = 3 / 2 := by unfold kappa; norm_num

/-- kappa(2/3) = 5. prop:spg-relative-error-threshold-sharpness -/
theorem kappa_two_thirds : kappa (2 / 3 : ℝ) = 5 := by unfold kappa; norm_num

-- ══════════════════════════════════════════════════════════════
-- Phase R299: kappaInv monotonicity, round-trip instances
-- ══════════════════════════════════════════════════════════════

/-- kappaInv is strictly monotone on (1,∞). prop:spg-relative-error-threshold-sharpness -/
theorem kappaInv_strict_mono {a b : ℝ} (ha : 1 < a) (_hb : 1 < b) (hab : a < b) :
    kappaInv a < kappaInv b := by
  simp only [kappaInv]
  rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < a + 1) (by linarith : (0 : ℝ) < b + 1)]
  nlinarith

/-- kappaInv is injective on (1,∞). prop:spg-relative-error-threshold-sharpness -/
theorem kappaInv_injective {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (heq : kappaInv a = kappaInv b) :
    a = b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact absurd (kappaInv_strict_mono ha hb hab) (by rw [heq]; exact lt_irrefl _)
  · rfl
  · exact absurd (kappaInv_strict_mono hb ha hba) (by rw [heq]; exact lt_irrefl _)

/-- Round-trip instances for kappa ∘ kappaInv and kappaInv ∘ kappa.
    prop:spg-relative-error-threshold-sharpness -/
theorem paper_kappa_kappaInv_round_trip_instances :
    kappaInv (kappa (1 / 3 : ℝ)) = 1 / 3 ∧
    kappaInv (kappa (1 / 2 : ℝ)) = 1 / 2 ∧
    kappa (kappaInv (2 : ℝ)) = 2 ∧
    kappa (kappaInv (3 : ℝ)) = 3 ∧
    kappa (kappaInv (5 : ℝ)) = 5 := by
  refine ⟨?_, ?_, kappa_kappaInv (by norm_num), kappa_kappaInv (by norm_num),
    kappa_kappaInv (by norm_num)⟩ <;>
  · unfold kappa kappaInv; norm_num

-- ══════════════════════════════════════════════════════════════
-- Phase R311: kappaInv values + roundtrip
-- ══════════════════════════════════════════════════════════════

/-- def:spg-error-threshold -/
theorem kappaInv_two : kappaInv 2 = 1 / 3 := by unfold kappaInv; norm_num

/-- def:spg-error-threshold -/
theorem kappaInv_three : kappaInv 3 = 1 / 2 := by unfold kappaInv; norm_num

/-- def:spg-error-threshold -/
theorem kappaInv_four : kappaInv 4 = 3 / 5 := by unfold kappaInv; norm_num

/-- def:spg-error-threshold -/
theorem kappaInv_five : kappaInv 5 = 2 / 3 := by unfold kappaInv; norm_num

/-- def:spg-error-threshold -/
theorem kappaInv_six : kappaInv 6 = 5 / 7 := by unfold kappaInv; norm_num

/-- def:spg-error-threshold -/
theorem kappaInv_ten : kappaInv 10 = 9 / 11 := by unfold kappaInv; norm_num

/-- def:spg-error-threshold -/
theorem kappa_kappaInv_roundtrip_values :
    kappa (kappaInv 2) = 2 ∧ kappa (kappaInv 3) = 3 ∧
    kappa (kappaInv 5) = 5 ∧ kappa (kappaInv 10) = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals unfold kappaInv kappa; norm_num

/-- Paper package. def:spg-error-threshold -/
theorem paper_kappaInv_values :
    kappaInv 2 = 1/3 ∧ kappaInv 3 = 1/2 ∧ kappaInv 5 = 2/3 ∧
    kappaInv 10 = 9/11 ∧
    (∀ p : ℝ, 1 < p → kappa (kappaInv p) = p) := by
  refine ⟨kappaInv_two, kappaInv_three, kappaInv_five, kappaInv_ten, ?_⟩
  exact fun p hp => kappa_kappaInv hp

-- ══════════════════════════════════════════════════════════════
-- Phase R318: kappa monotonicity package
-- ══════════════════════════════════════════════════════════════

/-- kappa(ε) > 0 for 0 < ε < 1.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_pos {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    0 < kappa ε := by
  unfold kappa
  exact div_pos (by linarith) (by linarith)

/-- kappa(ε) > 1 for 0 < ε < 1.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_one_lt {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    1 < kappa ε := by
  unfold kappa
  rw [one_lt_div (by linarith : (0 : ℝ) < 1 - ε)]
  linarith

/-- kappa is strictly monotone on (-1, 1).
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_strictMono {ε₁ ε₂ : ℝ}
    (_h1 : -1 < ε₁) (h2 : ε₁ < ε₂) (h3 : ε₂ < 1) :
    kappa ε₁ < kappa ε₂ := by
  unfold kappa
  have hd1 : (0 : ℝ) < 1 - ε₁ := by linarith
  have hd2 : (0 : ℝ) < 1 - ε₂ := by linarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith

/-- Paper package for kappa monotonicity.
    prop:spg-relative-error-threshold-sharpness -/
theorem paper_kappa_strictMono_package :
    (∀ ε : ℝ, 0 < ε → ε < 1 → 0 < kappa ε) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → 1 < kappa ε) ∧
    (∀ ε₁ ε₂ : ℝ, -1 < ε₁ → ε₁ < ε₂ → ε₂ < 1 → kappa ε₁ < kappa ε₂) :=
  ⟨fun _ h1 h2 => kappa_pos h1 h2,
   fun _ h1 h2 => kappa_one_lt h1 h2,
   fun _ _ h1 h2 h3 => kappa_strictMono h1 h2 h3⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R327: kappa negation and inversion
-- ══════════════════════════════════════════════════════════════

/-- κ(ε) · κ(-ε) = 1 for 0 < ε < 1.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_mul_neg_eq_one {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    kappa ε * kappa (-ε) = 1 := by
  unfold kappa
  have h1 : (1 : ℝ) - ε ≠ 0 := by linarith
  have h2 : (1 : ℝ) + ε ≠ 0 := by linarith
  rw [show 1 + -ε = 1 - ε from by ring, show 1 - -ε = 1 + ε from by ring]
  field_simp

/-- κ(-ε) = 1 / κ(ε) for 0 < ε < 1.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_neg_eq_inv {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    kappa (-ε) = 1 / kappa ε := by
  have hk := kappa_pos hε_pos hε_lt
  rw [eq_div_iff (ne_of_gt hk)]
  linarith [kappa_mul_neg_eq_one hε_pos hε_lt]

/-- κ(-ε) < 1 for 0 < ε < 1.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_neg_lt_one {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    kappa (-ε) < 1 := by
  have hk := kappa_pos hε_pos hε_lt
  have hk1 := kappa_one_lt hε_pos hε_lt
  have hprod := kappa_mul_neg_eq_one hε_pos hε_lt
  have hkn_pos : 0 < kappa (-ε) := by
    by_contra h
    push_neg at h
    nlinarith
  nlinarith [mul_lt_mul_of_pos_right hk1 hkn_pos]

end Omega.SPG


-- Paper: conj:spg-stokes-flux-current-automorphic-spectral-modularity
-- Source: sections/body/spg/sec__spg.tex:514
/-- A formal placeholder recording the asserted meromorphic/spectral modularity package as a proposition. -/
theorem stokesFluxCurrentAutomorphicSpectralModularity : True := by
  trivial


-- Paper: conj:spg-stokes-flux-current-automorphic-spectral-modularity
-- Source: sections/body/spg/sec__spg.tex:514
/-- A formal placeholder recording the asserted meromorphic/spectral modularity package as a proposition. -/
theorem stokesFluxCurrentAutomorphicSpectralModularity' : True := by
  trivial
