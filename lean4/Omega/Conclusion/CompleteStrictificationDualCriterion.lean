import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Vanishing of the total size-biased residual on a finite tower. -/
def zeroSizebiasedResidual {n : ℕ} (residual : Fin n → ℕ) : Prop :=
  ∑ i : Fin n, residual i = 0

/-- Layerwise rigidity version of the same size-biased residual condition. -/
def localSizeBiasRigidity {n : ℕ} (residual : Fin n → ℕ) : Prop :=
  ∀ i, residual i = 0

/-- Vanishing of the visible anomaly on a finite list of visible channels. -/
def zeroVisibleAnomaly {m : ℕ} (anomaly : Fin m → ℕ) : Prop :=
  ∑ i : Fin m, anomaly i = 0

/-- Terminal normal-form and CP-visible realization collapse to pointwise zero anomaly in this
finite bookkeeping model. -/
def terminalNormalFormCpVisibleRealization {m : ℕ} (anomaly : Fin m → ℕ) : Prop :=
  ∀ i, anomaly i = 0

lemma zero_sum_nat_iff_forall_zero {α : Type*} [Fintype α] (f : α → ℕ) :
    (∑ a, f a = 0) ↔ ∀ a, f a = 0 := by
  constructor
  · intro hsum a
    exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => Nat.zero_le (f b)).1 hsum a (by simp)
  · intro hzero
    simp [hzero]

/-- Conclusion-level complete strictification criterion: the two vanishing conditions are exactly
the conjunction of layerwise size-bias rigidity and terminal CP-visible normal form.
    thm:conclusion-complete-strictification-dual-criterion -/
theorem paper_conclusion_complete_strictification_dual_criterion
    {n m : ℕ} (residual : Fin n → ℕ) (anomaly : Fin m → ℕ) :
    (zeroSizebiasedResidual residual ∧ zeroVisibleAnomaly anomaly) ↔
      (localSizeBiasRigidity residual ∧ terminalNormalFormCpVisibleRealization anomaly) := by
  constructor
  · rintro ⟨hResidual, hAnomaly⟩
    exact ⟨(zero_sum_nat_iff_forall_zero residual).1 hResidual,
      (zero_sum_nat_iff_forall_zero anomaly).1 hAnomaly⟩
  · rintro ⟨hResidual, hAnomaly⟩
    exact ⟨(zero_sum_nat_iff_forall_zero residual).2 hResidual,
      (zero_sum_nat_iff_forall_zero anomaly).2 hAnomaly⟩

end Omega.Conclusion
