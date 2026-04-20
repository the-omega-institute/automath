import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.Zeta

/-- Exact last-bit counts in the dyadic binfold model. -/
def xiFoldbinLastBitCount (m : ℕ) : Bool → ℕ
  | false => Nat.fib (m + 1)
  | true => Nat.fib m

/-- The truncated dyadic capacity built from the exact last-bit counts and the two saturation
thresholds `φ⁻¹` and `1`. -/
noncomputable def xiFoldbinDyadicTruncatedCapacity (m : ℕ) (ζ : ℝ) : ℝ :=
  (xiFoldbinLastBitCount m false : ℝ) * min (1 / Real.goldenRatio) ζ +
    (xiFoldbinLastBitCount m true : ℝ) * min 1 ζ

/-- The critical-window limit profile obtained from the Fibonacci asymptotics of the two last-bit
sectors. -/
noncomputable def xiFoldbinDyadicCriticalWindowLimit (ζ : ℝ) : ℝ :=
  if ζ ≤ 1 / Real.goldenRatio then
    (Real.goldenRatio ^ 2 / Real.sqrt 5) * ζ
  else if ζ ≤ 1 then
    (1 + ζ) / Real.sqrt 5
  else
    2 / Real.sqrt 5

private theorem phiInv_lt_one : (1 / Real.goldenRatio : ℝ) < 1 := by
  have hsqrt5_gt_one : (1 : ℝ) < Real.sqrt 5 := by
    have hsqrt5_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  rw [Real.goldenRatio]
  field_simp
  nlinarith

private theorem phi_sq_mul_phi_inv :
    (Real.goldenRatio ^ 2 / Real.sqrt 5) * (1 / Real.goldenRatio) =
      Real.goldenRatio / Real.sqrt 5 := by
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  field_simp [hphi_ne, hsqrt5_ne]

/-- The exact last-bit counts are `|A₀| = F_{m+1}` and `|A₁| = F_m`; the truncated capacity
simplifies on the three dyadic regimes `ζ < φ⁻¹`, `φ⁻¹ < ζ < 1`, and `ζ > 1`; and the limiting
critical-window profile is the corresponding continuous three-phase law.
    thm:xi-foldbin-dyadic-capacity-critical-window-limit -/
theorem paper_xi_foldbin_dyadic_capacity_critical_window_limit :
    (∀ m, xiFoldbinLastBitCount m false = Nat.fib (m + 1)) ∧
      (∀ m, xiFoldbinLastBitCount m true = Nat.fib m) ∧
      (∀ m ⦃ζ : ℝ⦄, ζ ≤ 1 / Real.goldenRatio →
        xiFoldbinDyadicTruncatedCapacity m ζ = ((Nat.fib (m + 2) : ℕ) : ℝ) * ζ) ∧
      (∀ m ⦃ζ : ℝ⦄, 1 / Real.goldenRatio ≤ ζ → ζ ≤ 1 →
        xiFoldbinDyadicTruncatedCapacity m ζ =
          ((Nat.fib (m + 1) : ℕ) : ℝ) / Real.goldenRatio + (Nat.fib m : ℝ) * ζ) ∧
      (∀ m ⦃ζ : ℝ⦄, 1 ≤ ζ →
        xiFoldbinDyadicTruncatedCapacity m ζ =
          ((Nat.fib (m + 1) : ℕ) : ℝ) / Real.goldenRatio + (Nat.fib m : ℝ)) ∧
      (∀ ζ, ζ < 1 / Real.goldenRatio →
        xiFoldbinDyadicCriticalWindowLimit ζ = (Real.goldenRatio ^ 2 / Real.sqrt 5) * ζ) ∧
      (∀ ζ, 1 / Real.goldenRatio < ζ → ζ < 1 →
        xiFoldbinDyadicCriticalWindowLimit ζ = (1 + ζ) / Real.sqrt 5) ∧
      (∀ ζ, 1 < ζ →
        xiFoldbinDyadicCriticalWindowLimit ζ = 2 / Real.sqrt 5) ∧
      xiFoldbinDyadicCriticalWindowLimit (1 / Real.goldenRatio) =
        Real.goldenRatio / Real.sqrt 5 ∧
      xiFoldbinDyadicCriticalWindowLimit 1 = 2 / Real.sqrt 5 := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m ζ hζ
    have hζ_one : ζ ≤ 1 := le_of_lt (lt_of_le_of_lt hζ phiInv_lt_one)
    have hminPhi : min (1 / Real.goldenRatio) ζ = ζ := min_eq_right hζ
    have hminOne : min (1 : ℝ) ζ = ζ := min_eq_right hζ_one
    calc
      xiFoldbinDyadicTruncatedCapacity m ζ
          = (Nat.fib (m + 1) : ℝ) * ζ + (Nat.fib m : ℝ) * ζ := by
              rw [xiFoldbinDyadicTruncatedCapacity, hminPhi, hminOne]
              simp [xiFoldbinLastBitCount]
      _ = ((Nat.fib (m + 1) : ℝ) + (Nat.fib m : ℝ)) * ζ := by ring
      _ = ((Nat.fib (m + 2) : ℕ) : ℝ) * ζ := by
            have hfib : ((Nat.fib (m + 1) : ℕ) : ℝ) + (Nat.fib m : ℝ) =
                ((Nat.fib (m + 2) : ℕ) : ℝ) := by
              exact_mod_cast (by simpa [Nat.add_comm] using (Nat.fib_add_two (n := m)).symm)
            rw [hfib]
  · intro m ζ hζ0 hζ1
    have hminPhi : min (1 / Real.goldenRatio) ζ = 1 / Real.goldenRatio := by
      apply min_eq_left
      simpa [Real.goldenRatio] using hζ0
    have hminOne : min (1 : ℝ) ζ = ζ := min_eq_right hζ1
    rw [xiFoldbinDyadicTruncatedCapacity, hminPhi, hminOne]
    simp [xiFoldbinLastBitCount, div_eq_mul_inv, mul_comm]
  · intro m ζ hζ
    have hphiInv_le : (1 / Real.goldenRatio : ℝ) ≤ ζ := by
      have hphiInv_le_one : (1 / Real.goldenRatio : ℝ) ≤ 1 := le_of_lt phiInv_lt_one
      exact le_trans hphiInv_le_one hζ
    have hminPhi : min (1 / Real.goldenRatio) ζ = 1 / Real.goldenRatio := by
      apply min_eq_left
      simpa [Real.goldenRatio] using hphiInv_le
    have hminOne : min (1 : ℝ) ζ = 1 := min_eq_left hζ
    rw [xiFoldbinDyadicTruncatedCapacity, hminPhi, hminOne]
    simp [xiFoldbinLastBitCount, div_eq_mul_inv, mul_comm]
  · intro ζ hζ
    rw [xiFoldbinDyadicCriticalWindowLimit, if_pos (le_of_lt hζ)]
  · intro ζ hζ0 hζ1
    have hnot : ¬ ζ ≤ 1 / Real.goldenRatio := not_le_of_gt hζ0
    rw [xiFoldbinDyadicCriticalWindowLimit, if_neg hnot, if_pos (le_of_lt hζ1)]
  · intro ζ hζ
    have hnotPhi : ¬ ζ ≤ 1 / Real.goldenRatio := by
      exact not_le_of_gt (lt_trans phiInv_lt_one hζ)
    have hnotOne : ¬ ζ ≤ 1 := not_le_of_gt hζ
    rw [xiFoldbinDyadicCriticalWindowLimit, if_neg hnotPhi, if_neg hnotOne]
  · rw [xiFoldbinDyadicCriticalWindowLimit, if_pos le_rfl]
    exact phi_sq_mul_phi_inv
  · have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
    have hnot : ¬ (1 : ℝ) ≤ 1 / Real.goldenRatio := not_le_of_gt phiInv_lt_one
    rw [xiFoldbinDyadicCriticalWindowLimit, if_neg hnot, if_pos le_rfl]
    field_simp [hsqrt5_ne]
    norm_num

end Omega.Zeta
