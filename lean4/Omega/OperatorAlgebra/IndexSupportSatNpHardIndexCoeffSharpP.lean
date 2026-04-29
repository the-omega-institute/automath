import Omega.OperatorAlgebra.NpWatataniIndexSupportCharacterization

namespace Omega.OperatorAlgebra

section

variable {Formula Assignment : Type*} [Fintype Formula] [DecidableEq Formula]
  [Fintype Assignment] [DecidableEq Assignment]

/-- Paper label: `cor:index-support-sat-np-hard-index-coeff-sharpP`. -/
theorem index_support_sat_np_hard_index_coeff_sharpp_characterization
    (satEval : Formula → Assignment → Bool) :
    (∀ φ, verifierProjectorInSupport satEval φ ↔ ∃ a, satEval φ a = true) ∧
      (∀ φ, foldWatataniIndexElement (verifierFold satEval) φ = verifierWitnessCount satEval φ) := by
  simpa [and_comm] using paper_np_watatani_index_support_characterization satEval

end

end Omega.OperatorAlgebra
