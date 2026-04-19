import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The zero-temperature gap profile along the multiplicative ray. -/
noncomputable def zeroTemperatureGap (a : ℕ) : ℚ :=
  1 / (a : ℚ)

/-- The unitized zero-temperature gap is identically `1` away from `a = 0`. -/
noncomputable def unitizedGap (a : ℕ) : ℚ :=
  (a : ℚ) * zeroTemperatureGap a

/-- The loss cocycle attached to multiplying the scale by `b`. -/
noncomputable def lossCocycle (_a b : ℕ) : ℚ :=
  (b - 1 : ℚ)

private theorem unitizedGap_eq_one {a : ℕ} (ha : 0 < a) : unitizedGap a = 1 := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  rw [unitizedGap, zeroTemperatureGap]
  field_simp [haq]

private theorem zeroTemperatureGap_step {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    zeroTemperatureGap a - zeroTemperatureGap (a * b) =
      lossCocycle a b / (((a * b : ℕ) : ℚ)) := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  rw [zeroTemperatureGap, zeroTemperatureGap, lossCocycle, Nat.cast_mul]
  field_simp [haq, hbq]

private theorem lossCocycle_nonneg {a b : ℕ} (hb : 0 < b) : 0 ≤ lossCocycle a b := by
  have hb1 : (1 : ℚ) ≤ b := by exact_mod_cast Nat.succ_le_of_lt hb
  have hsub : 0 ≤ (b : ℚ) - 1 := by linarith
  simpa [lossCocycle] using hsub

/-- Chapter-local package for the zero-temperature gap on a multiplicative divisibility ray:
the unitized gap is `1`, the one-step gap is the loss cocycle divided by the new scale, the ray
sum telescopes, and vanishing of the step gap is equivalent to vanishing of the loss cocycle,
hence to `b = 1`. -/
def ZeroTemperatureGapDivisibilityRaySum : Prop :=
  (∀ a : ℕ, 0 < a → unitizedGap a = 1) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      zeroTemperatureGap a - zeroTemperatureGap (a * b) =
        lossCocycle a b / (((a * b : ℕ) : ℚ))) ∧
    (∀ a b : ℕ, 0 < b → 0 ≤ lossCocycle a b) ∧
    (∀ a b n : ℕ, 0 < a → 0 < b →
      zeroTemperatureGap a - zeroTemperatureGap (a * b ^ n) =
        Finset.sum (Finset.range n)
          (fun k => lossCocycle (a * b ^ k) b / (((a * b ^ (k + 1) : ℕ) : ℚ)))) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      (zeroTemperatureGap a = zeroTemperatureGap (a * b) ↔ lossCocycle a b = 0)) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → (lossCocycle a b = 0 ↔ b = 1))

/-- The zero-temperature gap satisfies the one-step divisibility identity
`r∞(a) - r∞(ab) = H_loss(a,b) / (ab)`. Summing the identity along the multiplicative ray
`a, ab, ab^2, ...` yields the telescoping series formula, and the nonnegative cocycle vanishes
exactly when `b = 1`.
    thm:pom-zero-temperature-gap-divisibility-ray-sum -/
theorem paper_pom_zero_temperature_gap_divisibility_ray_sum :
    ZeroTemperatureGapDivisibilityRaySum := by
  refine ⟨(fun a ha => unitizedGap_eq_one ha), (fun a b ha hb => zeroTemperatureGap_step ha hb), ?_, ?_, ?_, ?_⟩
  · intro a b hb
    exact lossCocycle_nonneg hb
  · intro a b n ha hb
    induction n with
    | zero =>
        simp [zeroTemperatureGap]
    | succ n ih =>
        have han : 0 < a * b ^ n := Nat.mul_pos ha (pow_pos hb n)
        have hstep := zeroTemperatureGap_step han hb
        calc
          zeroTemperatureGap a - zeroTemperatureGap (a * b ^ (n + 1))
              = (zeroTemperatureGap a - zeroTemperatureGap (a * b ^ n)) +
                  (zeroTemperatureGap (a * b ^ n) - zeroTemperatureGap ((a * b ^ n) * b)) := by
                  rw [pow_succ, Nat.mul_assoc]
                  ring
          _ = Finset.sum (Finset.range n)
                (fun k => lossCocycle (a * b ^ k) b / (((a * b ^ (k + 1) : ℕ) : ℚ))) +
                lossCocycle (a * b ^ n) b / (((a * b ^ (n + 1) : ℕ) : ℚ)) := by
                  rw [ih, hstep]
                  simp [pow_succ, Nat.mul_assoc]
          _ = Finset.sum (Finset.range (n + 1))
                (fun k => lossCocycle (a * b ^ k) b / (((a * b ^ (k + 1) : ℕ) : ℚ))) := by
                  rw [Finset.sum_range_succ]
  · intro a b ha hb
    constructor
    · intro hgap
      have hstep : lossCocycle a b / (((a * b : ℕ) : ℚ)) = 0 := by
        rw [← zeroTemperatureGap_step ha hb, sub_eq_zero]
        exact hgap
      have hden_ne : (((a * b : ℕ) : ℚ)) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Nat.mul_pos ha hb)
      exact (div_eq_zero_iff.mp hstep).elim id (fun h => False.elim (hden_ne h))
    · intro hloss
      rw [← sub_eq_zero, zeroTemperatureGap_step ha hb, hloss, zero_div]
  · intro a b ha hb
    constructor
    · intro hloss
      have hq : (b : ℚ) = 1 := by
        have hzero : (b : ℚ) - 1 = 0 := by simpa [lossCocycle] using hloss
        linarith
      exact_mod_cast hq
    · intro hb1
      simp [lossCocycle, hb1]

end Omega.POM
