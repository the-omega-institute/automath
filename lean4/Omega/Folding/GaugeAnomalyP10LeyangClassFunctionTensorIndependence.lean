import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

namespace Omega.Folding

open scoped BigOperators

/-- The finite average over `S₁₀ × S₃` factors as the product of the separate averages.
    thm:fold-gauge-anomaly-P10-leyang-class-function-tensor-independence -/
theorem paper_fold_gauge_anomaly_p10_leyang_class_function_tensor_independence
    (f : Equiv.Perm (Fin 10) → ℂ) (g : Equiv.Perm (Fin 3) → ℂ) :
    (∑ h : Equiv.Perm (Fin 10) × Equiv.Perm (Fin 3), f h.1 * g h.2) =
      (∑ σ : Equiv.Perm (Fin 10), f σ) * (∑ τ : Equiv.Perm (Fin 3), g τ) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ σ : Equiv.Perm (Fin 10), ∑ τ : Equiv.Perm (Fin 3), f σ * g τ) =
        ∑ σ : Equiv.Perm (Fin 10), f σ * (∑ τ : Equiv.Perm (Fin 3), g τ) := by
          simp [Finset.mul_sum]
    _ = (∑ σ : Equiv.Perm (Fin 10), f σ) * (∑ τ : Equiv.Perm (Fin 3), g τ) := by
          rw [Finset.sum_mul]

end Omega.Folding
