import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

private theorem residual_budget_eq (b r k t : ℕ) (hk : k ≤ r) :
    (2 ^ (b * k)) * ((2 ^ (b * (r - k))) * t) = (2 ^ (b * r)) * t := by
  have hexp : b * k + b * (r - k) = b * r := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hk]
  calc
    (2 ^ (b * k)) * ((2 ^ (b * (r - k))) * t)
        = ((2 ^ (b * k)) * 2 ^ (b * (r - k))) * t := by rw [Nat.mul_assoc]
    _ = (2 ^ (b * r)) * t := by rw [← pow_add, hexp]

private theorem residual_register_with_t_lower_bound (b r k t R : ℕ) (hk : k ≤ r)
    (hinj : ∃ f : Fin ((2 ^ (b * r)) * t) → Fin ((2 ^ (b * k)) * R), Function.Injective f) :
    (2 ^ (b * (r - k))) * t ≤ R := by
  have hcard : (2 ^ (b * r)) * t ≤ (2 ^ (b * k)) * R :=
    phaseResidualBudget_lower_bound_finite b r k t R hinj
  have hmul : (2 ^ (b * k)) * ((2 ^ (b * (r - k))) * t) ≤ (2 ^ (b * k)) * R := by
    simpa [residual_budget_eq b r k t hk] using hcard
  have hpos : 0 < 2 ^ (b * k) := by positivity
  exact Nat.le_of_mul_le_mul_left hmul hpos

/-- Corrected finite residual-entropy lower bound: the logarithmic bound needs the uniform window
support to be nonempty and the residual register to carry the deficit `r - k`.
    thm:cdim-residual-entropy-lower-bound -/
theorem paper_cdim_residual_entropy_lower_bound_corrected (b r k t R : Nat) (ht : 0 < t)
    (hk : k ≤ r)
    (hinj : Exists fun f : Fin ((2 ^ (b * r)) * t) -> Fin ((2 ^ (b * k)) * R) =>
      Function.Injective f) :
    (r - k) * b + Nat.log 2 t <= Nat.log 2 R := by
  have hR : 2 ^ (b * (r - k)) * t ≤ R :=
    residual_register_with_t_lower_bound b r k t R hk hinj
  have hpow : 2 ^ ((r - k) * b + Nat.log 2 t) ≤ R := by
    calc
      2 ^ ((r - k) * b + Nat.log 2 t)
          = 2 ^ ((r - k) * b) * 2 ^ Nat.log 2 t := by rw [pow_add]
      _ ≤ 2 ^ ((r - k) * b) * t := by
        exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 ht.ne')
      _ = 2 ^ (b * (r - k)) * t := by rw [Nat.mul_comm (r - k) b]
      _ ≤ R := hR
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow

/-- The unqualified signature requested in the paper draft is false as written.
    A concrete counterexample is `b = 1`, `r = 1`, `k = 2`, `t = 4`, `R = 2`.
    thm:cdim-residual-entropy-lower-bound -/
theorem paper_cdim_residual_entropy_lower_bound_counterexample :
    (Exists fun f : Fin ((2 ^ (1 * 1)) * 4) -> Fin ((2 ^ (1 * 2)) * 2) =>
      Function.Injective f) ∧
      ¬ ((1 - 2) * 1 + Nat.log 2 4 <= Nat.log 2 2) := by
  refine ⟨?_, by decide⟩
  refine ⟨Fin.castLE (by decide), ?_⟩
  exact Fin.castLE_injective (by decide)

/-- Saturation of the phase-space entropy budget. -/
def phaseUniformOnFullSpace (phaseEntropy phaseSpaceEntropy : ℕ) : Prop :=
  phaseEntropy = phaseSpaceEntropy

/-- Equality in the joint-entropy subadditivity step. -/
def phaseResidualIndependent (jointEntropy phaseEntropy residualEntropy : ℕ) : Prop :=
  jointEntropy = phaseEntropy + residualEntropy

private theorem residual_entropy_lower_bound_of_chain
    (jointEntropy phaseEntropy residualEntropy phaseSpaceEntropy targetEntropy : ℕ)
    (hjoint : jointEntropy = phaseSpaceEntropy + targetEntropy)
    (hphase : phaseEntropy ≤ phaseSpaceEntropy)
    (hsubadd : jointEntropy ≤ phaseEntropy + residualEntropy) :
    targetEntropy ≤ residualEntropy := by
  omega

/-- Equality in the residual-entropy lower bound occurs exactly when the phase component saturates
the full phase-space budget and the phase/residual coordinates realize equality in subadditivity. -/
theorem paper_cdim_residual_entropy_lower_bound_rigidity
    (jointEntropy phaseEntropy residualEntropy phaseSpaceEntropy targetEntropy : ℕ)
    (hjoint : jointEntropy = phaseSpaceEntropy + targetEntropy)
    (hphase : phaseEntropy ≤ phaseSpaceEntropy)
    (hsubadd : jointEntropy ≤ phaseEntropy + residualEntropy) :
    residualEntropy = targetEntropy ↔
      phaseUniformOnFullSpace phaseEntropy phaseSpaceEntropy ∧
        phaseResidualIndependent jointEntropy phaseEntropy residualEntropy := by
  constructor
  · intro hEq
    have hsubadd' : phaseSpaceEntropy + targetEntropy ≤ phaseEntropy + targetEntropy := by
      simp [hjoint, hEq] at hsubadd ⊢
      exact hsubadd
    have hphaseEq : phaseEntropy = phaseSpaceEntropy := by
      omega
    have hindep : jointEntropy = phaseEntropy + residualEntropy := by
      apply le_antisymm hsubadd
      simp [hjoint, hEq, hphaseEq]
    exact ⟨hphaseEq, hindep⟩
  · rintro ⟨hphaseEq, hindep⟩
    have hsum : phaseSpaceEntropy + targetEntropy = phaseSpaceEntropy + residualEntropy := by
      calc
        phaseSpaceEntropy + targetEntropy = jointEntropy := by simp [hjoint]
        _ = phaseEntropy + residualEntropy := hindep
        _ = phaseSpaceEntropy + residualEntropy := by rw [hphaseEq]
    exact Nat.add_left_cancel hsum.symm

end Omega.CircleDimension
