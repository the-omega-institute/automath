import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The Hellinger sum appearing in the Rényi-`1/2` identity. -/
noncomputable def pomHellingerHalfSum {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  ∑ a, Real.sqrt (w a)

/-- The order-`1/2` Rényi entropy written in Hellinger-sum form. -/
noncomputable def pomRenyiHalfEntropy {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  2 * Real.log (pomHellingerHalfSum w)

/-- Tensor-product weights on a product alphabet. -/
def pomTensorWeight {α β : Type*} (w : α → ℝ) (v : β → ℝ) : α × β → ℝ :=
  fun ab => w ab.1 * v ab.2

@[simp] theorem pomRenyiHalfEntropy_unfold {α : Type*} [Fintype α] (w : α → ℝ) :
    pomRenyiHalfEntropy w = 2 * Real.log (pomHellingerHalfSum w) := rfl

theorem pomHellingerHalfSum_tensor {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ a, 0 ≤ w a) (_hv : ∀ b, 0 ≤ v b) :
    pomHellingerHalfSum (pomTensorWeight w v) =
      pomHellingerHalfSum w * pomHellingerHalfSum v := by
  classical
  unfold pomHellingerHalfSum pomTensorWeight
  rw [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, Real.sqrt (w a * v b) = ∑ a, ∑ b, Real.sqrt (w a) * Real.sqrt (v b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [Real.sqrt_mul (hw a)]
    _ = ∑ a, Real.sqrt (w a) * ∑ b, Real.sqrt (v b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.mul_sum]
    _ = (∑ a, Real.sqrt (w a)) * ∑ b, Real.sqrt (v b) := by
      rw [← Finset.sum_mul]

theorem pomRenyiHalfEntropy_tensor_additivity {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ a, 0 ≤ w a) (hv : ∀ b, 0 ≤ v b)
    (hwpos : 0 < pomHellingerHalfSum w) (hvpos : 0 < pomHellingerHalfSum v) :
    pomRenyiHalfEntropy (pomTensorWeight w v) =
      pomRenyiHalfEntropy w + pomRenyiHalfEntropy v := by
  rw [pomRenyiHalfEntropy_unfold, pomRenyiHalfEntropy_unfold, pomRenyiHalfEntropy_unfold]
  rw [pomHellingerHalfSum_tensor w v hw hv]
  rw [Real.log_mul hwpos.ne' hvpos.ne']
  ring

/-- Proposition package for the Rényi-`1/2`/Hellinger identity and tensor additivity.
    prop:pom-renyi-half-hellinger-identity-tensor-additivity -/
def paper_pom_renyi_half_hellinger_identity_tensor_additivity_statement : Prop :=
  ∀ {α β : Type*} [Fintype α] [Fintype β], ∀ (w : α → ℝ) (v : β → ℝ),
    (∀ a, 0 ≤ w a) →
    (∀ b, 0 ≤ v b) →
    0 < pomHellingerHalfSum w →
    0 < pomHellingerHalfSum v →
    pomRenyiHalfEntropy w = 2 * Real.log (pomHellingerHalfSum w) ∧
      pomHellingerHalfSum (pomTensorWeight w v) =
        pomHellingerHalfSum w * pomHellingerHalfSum v ∧
      pomRenyiHalfEntropy (pomTensorWeight w v) =
        pomRenyiHalfEntropy w + pomRenyiHalfEntropy v

theorem paper_pom_renyi_half_hellinger_identity_tensor_additivity :
    paper_pom_renyi_half_hellinger_identity_tensor_additivity_statement := by
  intro α β _ _ w v hw hv hwpos hvpos
  refine ⟨pomRenyiHalfEntropy_unfold w, pomHellingerHalfSum_tensor w v hw hv, ?_⟩
  exact pomRenyiHalfEntropy_tensor_additivity w v hw hv hwpos hvpos

end Omega.POM
