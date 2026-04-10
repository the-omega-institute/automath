import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Time-reversal sign mod 12 periodicity

The sign of the time-reversal involution ι_ℓ on Ind(P_ℓ) depends only
on ℓ mod 12. The sign equals (-1)^{(|Ind(P_ℓ)| - Fix(ι_ℓ))/2}, where
|Ind(P_ℓ)| = F(ℓ+2) and Fix(ι_ℓ) depends on parity of ℓ.
-/

namespace Omega.POM.ToggleOrder

/-- Fixed-point count of the time-reversal involution:
    Fix(ι_ℓ) = F(⌊ℓ/2⌋+1) if ℓ even, F(⌊ℓ/2⌋+3) if ℓ odd.
    thm:pom-toggle-time-reversal-sign-mod12 -/
def timeReversalFix (ℓ : Nat) : Nat :=
  let k := ℓ / 2
  if ℓ % 2 = 0 then Nat.fib (k + 1) else Nat.fib (k + 3)

/-- The sign exponent: (F(ℓ+2) - Fix(ℓ)) / 2.
    thm:pom-toggle-time-reversal-sign-mod12 -/
def timeReversalSignExp (ℓ : Nat) : Nat :=
  (Nat.fib (ℓ + 2) - timeReversalFix ℓ) / 2

/-- Positive sign positions: sgn(ι_ℓ) = +1 for ℓ ≡ 0,1,5,9,10,11 (mod 12).
    Verified for one complete period ℓ = 1..12.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_positive :
    timeReversalSignExp 1 % 2 = 0 ∧ timeReversalSignExp 5 % 2 = 0 ∧
    timeReversalSignExp 9 % 2 = 0 ∧ timeReversalSignExp 10 % 2 = 0 ∧
    timeReversalSignExp 11 % 2 = 0 ∧ timeReversalSignExp 12 % 2 = 0 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Negative sign positions: sgn(ι_ℓ) = -1 for ℓ ≡ 2,3,4,6,7,8 (mod 12).
    Verified for one complete period ℓ = 2..8.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_negative :
    timeReversalSignExp 2 % 2 = 1 ∧ timeReversalSignExp 3 % 2 = 1 ∧
    timeReversalSignExp 4 % 2 = 1 ∧ timeReversalSignExp 6 % 2 = 1 ∧
    timeReversalSignExp 7 % 2 = 1 ∧ timeReversalSignExp 8 % 2 = 1 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Paper package: time-reversal sign mod 12 periodicity.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem paper_pom_toggle_time_reversal_sign_mod12 :
    (∀ ℓ ∈ ({1, 5, 9, 10, 11, 12} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 0) ∧
    (∀ ℓ ∈ ({2, 3, 4, 6, 7, 8} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 1) := by
  constructor <;> intro ℓ hℓ <;> fin_cases hℓ <;>
    simp only [timeReversalSignExp, timeReversalFix] <;> native_decide

/-- Scan-order intrinsic period lcm closed-form seeds.
    thm:pom-toggle-scan-order-closed-form -/
theorem paper_pom_toggle_scan_order_seeds :
    Nat.lcm 3 5 = 15 ∧
    Nat.lcm (Nat.lcm 2 3) 8 = 24 ∧
    Nat.lcm (Nat.lcm 3 11) 7 = 231 ∧
    Nat.lcm (Nat.lcm (Nat.lcm 2 3) 14) 10 = 210 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Scan-element orbit length spectrum seeds.
    thm:pom-toggle-scan-orbit-length-spectrum -/
theorem paper_pom_toggle_orbit_length_spectrum_seeds :
    (3 * 4 - 3 - 4 * 1 = 5 ∧ Nat.gcd 1 1 = 1) ∧
    (3 * 5 - 3 - 4 * 1 = 8 ∧ Nat.gcd 2 1 = 1) ∧
    (3 * 6 - 3 - 4 * 1 = 11 ∧ 3 * 6 - 3 - 4 * 2 = 7) ∧
    (Nat.gcd 3 1 = 1 ∧ Nat.gcd 1 2 = 1) ∧
    (3 * 4 - 7 = 5 ∧ 3 * 5 - 7 = 8 ∧ 3 * 6 - 7 = 11 ∧ 3 * 7 - 7 = 14) := by
  refine ⟨⟨by omega, by decide⟩, ⟨by omega, by decide⟩,
         ⟨by omega, by omega⟩, ⟨by decide, by decide⟩,
         ⟨by omega, by omega, by omega, by omega⟩⟩

-- Phase R604: Time-reversal second period verification
-- ══════════════════════════════════════════════════════════════

/-- Positive sign positions in second period (ℓ = 13..24).
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_positive_period2 :
    timeReversalSignExp 13 % 2 = 0 ∧ timeReversalSignExp 17 % 2 = 0 ∧
    timeReversalSignExp 21 % 2 = 0 ∧ timeReversalSignExp 22 % 2 = 0 ∧
    timeReversalSignExp 23 % 2 = 0 ∧ timeReversalSignExp 24 % 2 = 0 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Negative sign positions in second period (ℓ = 14..20).
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_negative_period2 :
    timeReversalSignExp 14 % 2 = 1 ∧ timeReversalSignExp 15 % 2 = 1 ∧
    timeReversalSignExp 16 % 2 = 1 ∧ timeReversalSignExp 18 % 2 = 1 ∧
    timeReversalSignExp 19 % 2 = 1 ∧ timeReversalSignExp 20 % 2 = 1 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Fix(ι_ℓ) ≤ F(ℓ+2) for all ℓ ≥ 1.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversalFix_le_total (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    timeReversalFix ℓ ≤ Nat.fib (ℓ + 2) := by
  unfold timeReversalFix
  split
  · -- even case: Fix = F(ℓ/2 + 1) ≤ F(ℓ + 2)
    exact Nat.fib_mono (by omega)
  · -- odd case: Fix = F(ℓ/2 + 3) ≤ F(ℓ + 2)
    exact Nat.fib_mono (by omega)

/-- Paper package: two complete periods of time-reversal sign mod 12.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem paper_pom_toggle_time_reversal_two_periods :
    (∀ ℓ ∈ ({1,5,9,10,11,12,13,17,21,22,23,24} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 0) ∧
    (∀ ℓ ∈ ({2,3,4,6,7,8,14,15,16,18,19,20} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 1) := by
  constructor <;> intro ℓ hℓ <;> fin_cases hℓ <;>
    simp only [timeReversalSignExp, timeReversalFix] <;> native_decide

end Omega.POM.ToggleOrder
