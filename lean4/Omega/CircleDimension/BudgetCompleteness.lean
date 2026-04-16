import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

private theorem phase_only_budget_le (b r k t : ℕ) (hrk : r ≤ k) :
    (2 ^ (b * r)) * t ≤ (2 ^ (b * k)) * t := by
  have hpow : 2 ^ (b * r) ≤ 2 ^ (b * k) := by
    exact pow_le_pow_right' (by decide : 1 ≤ 2) (Nat.mul_le_mul_left b hrk)
  exact Nat.mul_le_mul_right t hpow

private theorem phase_residual_budget_eq (b r k t : ℕ) (hkr : k < r) :
    (2 ^ (b * k)) * ((2 ^ (b * (r - k))) * t) = (2 ^ (b * r)) * t := by
  have hk_le : k ≤ r := Nat.le_of_lt hkr
  have hexp : b * k + b * (r - k) = b * r := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hk_le]
  calc
    (2 ^ (b * k)) * ((2 ^ (b * (r - k))) * t)
        = ((2 ^ (b * k)) * 2 ^ (b * (r - k))) * t := by rw [Nat.mul_assoc]
    _ = (2 ^ (b * r)) * t := by rw [← pow_add, hexp]

/-- Paper-facing finite completeness package for the phase/residual budget split:
every injective encoding obeys the lower bound, and the lower bound is attained both by padding
phase channels when `k ≥ r` and by moving `r - k` coordinates into an explicit residual register
when `k < r`.
    thm:cdim-budget-completeness -/
theorem paper_cdim_budget_completeness :
    (∀ b r k t R : ℕ,
      (∃ f : Fin ((2 ^ (b * r)) * t) → Fin ((2 ^ (b * k)) * R), Function.Injective f) →
        (2 ^ (b * r)) * t ≤ (2 ^ (b * k)) * R) ∧
    (∀ b r k t : ℕ, r ≤ k →
      ∃ f : Fin ((2 ^ (b * r)) * t) → Fin ((2 ^ (b * k)) * t), Function.Injective f) ∧
    (∀ b r k t : ℕ, k < r →
      ∃ f : Fin ((2 ^ (b * r)) * t) →
          Fin ((2 ^ (b * k)) * ((2 ^ (b * (r - k))) * t)),
        Function.Injective f) := by
  refine ⟨phaseResidualBudget_lower_bound_finite, ?_, ?_⟩
  · intro b r k t hrk
    refine ⟨Fin.castLE (phase_only_budget_le b r k t hrk), ?_⟩
    exact Fin.castLE_injective (phase_only_budget_le b r k t hrk)
  · intro b r k t hkr
    refine ⟨Fin.cast (phase_residual_budget_eq b r k t hkr).symm, ?_⟩
    exact Fin.cast_injective _

end Omega.CircleDimension
