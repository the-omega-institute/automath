import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

open Finset

/-- Paper label: `thm:conclusion-schur-subgroup-average-fixed-vector-tomography`.
The Schur expansion is unchanged after replacing each character-average coefficient by the
equal fixed-vector multiplicity coefficient pointwise inside the finite sum. -/
theorem paper_conclusion_schur_subgroup_average_fixed_vector_tomography {ι M : Type*}
    [Fintype ι] (A : M → ℝ) (T : ι → M → ℝ) (characterAverage fixedDim : ι → ℝ)
    (hTraceFixed : ∀ i, characterAverage i = fixedDim i)
    (hSchurExpansion : ∀ m, A m = ∑ i, characterAverage i * T i m) :
    ∀ m, A m = ∑ i, fixedDim i * T i m := by
  intro m
  rw [hSchurExpansion m]
  exact sum_congr rfl (fun i _ => by rw [hTraceFixed i])

end Omega.Conclusion
