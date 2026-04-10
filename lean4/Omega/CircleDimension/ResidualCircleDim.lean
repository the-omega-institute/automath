import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Per-depth residual circle-dimension (discrete version).
    def:cdim-residual-circle-dimension -/
def residualCdimAt (R : Nat → Nat) (b : Nat) : Nat :=
  Nat.log 2 (R b) / b

/-- Pointwise monotonicity of residual circle dimension.
    prop:cdim-residual-circle-dimension-laws -/
theorem residualCdimAt_mono_of_card_le (R S : Nat → Nat) (b : Nat)
    (h : R b ≤ S b) :
    residualCdimAt R b ≤ residualCdimAt S b := by
  unfold residualCdimAt
  exact Nat.div_le_div_right (Nat.log_mono_right h)

/-- 2^a · 2^b = 2^(a+b).
    prop:cdim-residual-circle-dimension-laws -/
theorem residual_register_pow_add (a b : Nat) : 2 ^ a * 2 ^ b = 2 ^ (a + b) := by
  rw [pow_add]

/-- Log of pure 2-power product is additive.
    prop:cdim-residual-circle-dimension-laws -/
theorem residual_log_product_eq_sum_of_powers (f g : Nat → Nat) (b : Nat) :
    Nat.log 2 (2 ^ f b * 2 ^ g b) = Nat.log 2 (2 ^ f b) + Nat.log 2 (2 ^ g b) := by
  rw [← pow_add, Nat.log_pow (by norm_num : 1 < 2),
      Nat.log_pow (by norm_num : 1 < 2), Nat.log_pow (by norm_num : 1 < 2)]

/-- Paper package: residual circle-dimension core laws.
    prop:cdim-residual-circle-dimension-laws -/
theorem paper_cdim_residual_circle_dim_laws :
    (∀ R S : Nat → Nat, ∀ b : Nat, R b ≤ S b →
      residualCdimAt R b ≤ residualCdimAt S b) ∧
    (∀ a b : Nat, 2 ^ a * 2 ^ b = 2 ^ (a + b)) ∧
    (∀ f g : Nat → Nat, ∀ b : Nat,
      Nat.log 2 (2 ^ f b * 2 ^ g b) =
        Nat.log 2 (2 ^ f b) + Nat.log 2 (2 ^ g b)) :=
  ⟨residualCdimAt_mono_of_card_le,
   residual_register_pow_add,
   residual_log_product_eq_sum_of_powers⟩

/-- residualCdimAt of a pure 2-power register is f b / b.
    prop:cdim-residual-circle-dimension-laws -/
theorem residualCdimAt_pow_two (f : Nat → Nat) (b : Nat) (_hb : 0 < b) :
    residualCdimAt (fun n => 2 ^ f n) b = f b / b := by
  unfold residualCdimAt
  rw [Nat.log_pow (by norm_num : 1 < 2)]

/-- residualCdimAt vanishes when the register cardinality is zero.
    prop:cdim-residual-circle-dimension-laws -/
theorem residualCdimAt_eq_zero_of_card_zero (R : Nat → Nat) (b : Nat)
    (h : R b = 0) :
    residualCdimAt R b = 0 := by
  unfold residualCdimAt
  rw [h]
  simp

/-- Extended residualCdimAt behavior package: monotone, vanishes at zero,
    pure 2-power formula, log additivity, and product residual formula.
    prop:cdim-residual-circle-dimension-laws -/
theorem paper_cdim_residual_extended_package :
    (∀ R S : Nat → Nat, ∀ b : Nat, R b ≤ S b →
      residualCdimAt R b ≤ residualCdimAt S b) ∧
    (∀ R : Nat → Nat, ∀ b : Nat, R b = 0 →
      residualCdimAt R b = 0) ∧
    (∀ f : Nat → Nat, ∀ b : Nat, 0 < b →
      residualCdimAt (fun n => 2 ^ f n) b = f b / b) ∧
    (∀ a b : Nat, 2 ^ a * 2 ^ b = 2 ^ (a + b)) ∧
    (∀ f g : Nat → Nat, ∀ b : Nat,
      Nat.log 2 (2 ^ f b * 2 ^ g b) =
        Nat.log 2 (2 ^ f b) + Nat.log 2 (2 ^ g b)) ∧
    (∀ f g : Nat → Nat, ∀ b : Nat, 0 < b →
      residualCdimAt (fun n => 2 ^ f n * 2 ^ g n) b =
        (f b + g b) / b) := by
  refine ⟨residualCdimAt_mono_of_card_le,
          residualCdimAt_eq_zero_of_card_zero,
          residualCdimAt_pow_two,
          residual_register_pow_add,
          residual_log_product_eq_sum_of_powers,
          ?_⟩
  intro f g b _hb
  unfold residualCdimAt
  show Nat.log 2 (2 ^ f b * 2 ^ g b) / b = (f b + g b) / b
  rw [← pow_add, Nat.log_pow (by norm_num : 1 < 2)]

-- Phase R605: Abelianization bottleneck
-- ══════════════════════════════════════════════════════════════

/-- 2^(b·k) < 2^(b·r) when k < r and b > 0.
    cor:cdim-abelianization-bottleneck -/
theorem abelianization_bottleneck (r k b : ℕ) (hrk : k < r) (hb : 0 < b) :
    2 ^ (b * k) < 2 ^ (b * r) := by
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
  exact Nat.mul_lt_mul_of_pos_left hrk hb

/-- Special case r=3, k=1: 2^b < 2^(3b).
    cor:cdim-abelianization-bottleneck -/
theorem abelianization_bottleneck_r3_k1 (b : ℕ) (hb : 0 < b) :
    2 ^ b < 2 ^ (3 * b) := by
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
  nlinarith

/-- Residual register lower bound from injection constraint.
    cor:cdim-abelianization-bottleneck -/
theorem residual_register_lower_bound (r k b R : ℕ)
    (hinj : 2 ^ (b * r) ≤ 2 ^ (b * k) * R) :
    2 ^ (b * (r - k)) ≤ R := by
  by_cases h : k ≤ r
  · have hexp : b * k + b * (r - k) = b * r := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' h]
    have hpow : 2 ^ (b * k) * 2 ^ (b * (r - k)) = 2 ^ (b * r) := by
      rw [← pow_add, hexp]
    have hpos : 0 < 2 ^ (b * k) := Nat.pos_of_ne_zero (by positivity)
    exact Nat.le_of_mul_le_mul_left (hpow ▸ hinj) hpos
  · simp only [show r - k = 0 from by omega, Nat.mul_zero, pow_zero]
    by_contra hR
    push_neg at hR
    interval_cases R
    simp at hinj

/-- Paper seeds: abelianization bottleneck concrete values.
    cor:cdim-abelianization-bottleneck -/
theorem paper_cdim_abelianization_bottleneck_seeds :
    (2 ^ 3 < 2 ^ 6) ∧
    (2 ^ (3 * 1) ≤ 2 ^ (3 * 1) * 8) ∧
    (2 ^ 2 < 2 ^ 6) ∧
    (2 ^ (1 * 1) ≤ 2 ^ (1 * 1) * 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end Omega.CircleDimension
