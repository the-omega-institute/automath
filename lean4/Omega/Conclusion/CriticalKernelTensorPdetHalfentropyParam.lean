import Mathlib.Tactic
import Omega.Conclusion.CriticalKernelPdetUniformMinimizer

namespace Omega.Conclusion

/-- Concrete tensor-product data for the critical-kernel pseudodeterminant formula.  The tensor
closed form is recorded before rewriting the tensor laws, and `halfEntropyParamForm` is the same
quantity expressed through the half-entropy single parameter. -/
structure conclusion_critical_kernel_tensor_pdet_halfentropy_param_data where
  baseCardinality : ℕ
  tensorLevel : ℕ
  baseA : ℝ
  baseC : ℝ
  tensorGeometricPdet : ℝ
  halfEntropyParamForm : ℝ
  tensorPdetClosed :
    tensorGeometricPdet =
      (baseA ^ tensorLevel) ^ (baseCardinality ^ tensorLevel - 2) /
        (((1 + baseC) ^ tensorLevel - 1) ^ (baseCardinality ^ tensorLevel - 1))
  halfEntropyParamClosed :
    halfEntropyParamForm = tensorGeometricPdet

namespace conclusion_critical_kernel_tensor_pdet_halfentropy_param_data

/-- After substituting the tensor laws, the geometric-mean-normalized pseudodeterminant is a
single-parameter half-entropy expression. -/
def tensor_pdet_halfentropy_param
    (D : conclusion_critical_kernel_tensor_pdet_halfentropy_param_data) : Prop :=
  D.tensorGeometricPdet =
      D.baseA ^ (D.tensorLevel * (D.baseCardinality ^ D.tensorLevel - 2)) /
        (((1 + D.baseC) ^ D.tensorLevel - 1) ^
          (D.baseCardinality ^ D.tensorLevel - 1)) ∧
    D.halfEntropyParamForm =
      D.baseA ^ (D.tensorLevel * (D.baseCardinality ^ D.tensorLevel - 2)) /
        (((1 + D.baseC) ^ D.tensorLevel - 1) ^
          (D.baseCardinality ^ D.tensorLevel - 1))

end conclusion_critical_kernel_tensor_pdet_halfentropy_param_data

/-- Paper label: `thm:conclusion-critical-kernel-tensor-pdet-halfentropy-param`. Substituting
`A(w^{⊗k}) = A(w)^k` into the tensor pseudodeterminant closed form rewrites the tower as the
stated half-entropy single-parameter expression. -/
theorem paper_conclusion_critical_kernel_tensor_pdet_halfentropy_param
    (D : conclusion_critical_kernel_tensor_pdet_halfentropy_param_data) :
    D.tensor_pdet_halfentropy_param := by
  have hPdet :
      D.tensorGeometricPdet =
        D.baseA ^ (D.tensorLevel * (D.baseCardinality ^ D.tensorLevel - 2)) /
          (((1 + D.baseC) ^ D.tensorLevel - 1) ^
            (D.baseCardinality ^ D.tensorLevel - 1)) := by
    calc
      D.tensorGeometricPdet =
          (D.baseA ^ D.tensorLevel) ^ (D.baseCardinality ^ D.tensorLevel - 2) /
            (((1 + D.baseC) ^ D.tensorLevel - 1) ^
              (D.baseCardinality ^ D.tensorLevel - 1)) :=
        D.tensorPdetClosed
      _ =
          D.baseA ^ (D.tensorLevel * (D.baseCardinality ^ D.tensorLevel - 2)) /
            (((1 + D.baseC) ^ D.tensorLevel - 1) ^
              (D.baseCardinality ^ D.tensorLevel - 1)) := by
        rw [pow_mul]
  exact ⟨hPdet, D.halfEntropyParamClosed.trans hPdet⟩

end Omega.Conclusion
