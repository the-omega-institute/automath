import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hypercube-joint-chiral-tensor-factorization`. -/
theorem paper_conclusion_hypercube_joint_chiral_tensor_factorization
    (m r nPlus : ℕ) (hr : 2 * r ≤ m) (hnPlus : nPlus ≤ r) :
    Module.finrank ℂ
        (TensorProduct ℂ (Fin (2 ^ (m - 2 * r)) → ℂ) (Fin (3 ^ nPlus) → ℂ)) =
      2 ^ (m - 2 * r) * 3 ^ nPlus := by
  let _ := hr
  let _ := hnPlus
  rw [Module.finrank_tensorProduct, Module.finrank_fin_fun, Module.finrank_fin_fun]

end Omega.Conclusion
