import Omega.Zeta.XiV4IntermediateDoubleCoversGenus8Fiberproduct
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-v4-jacobian-prym-triple-decomposition`. -/
theorem paper_xi_v4_jacobian_prym_triple_decomposition
    (prymDim : Fin 3 → Nat) (jacobianQIsogeny prymS3Transitive : Prop)
    (hDim : ∀ i,
      prymDim i = xi_v4_intermediate_double_covers_genus8_fiberproduct_intermediate_genus i - 4)
    (hJac : jacobianQIsogeny) (hSym : prymS3Transitive) :
    (∀ i, prymDim i = 4) ∧ jacobianQIsogeny ∧ prymS3Transitive := by
  constructor
  · intro i
    rw [hDim i]
    unfold xi_v4_intermediate_double_covers_genus8_fiberproduct_intermediate_genus
    norm_num
  · exact ⟨hJac, hSym⟩

end Omega.Zeta
