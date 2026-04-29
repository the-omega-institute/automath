import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInputDefectEntropy
import Omega.SyncKernelWeighted.RealInput40InputMemoryMarginal
import Omega.SyncKernelWeighted.RealInput40ResetWord

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

/-- Paper label: `prop:real-input-40-input-measure-rigid`. In the concrete real-input-`40`
surrogate, the reset word is available, the input-memory marginal is explicitly rigid, and the
defect-entropy control places the reset cylinder inside the ambient shift with no entropy loss. -/
theorem paper_real_input_40_input_measure_rigid :
    RealInput40ResetWordStatement ∧
      RealInput40InputMemoryMarginalClosedForm ∧
      real_input_defect_entropy_subshift 5 ⊆ real_input_defect_entropy_ambient ∧
      real_input_defect_entropy_value 5 ≤ real_input_defect_entropy_value 6 := by
  rcases paper_real_input_defect_entropy 5 with ⟨_, _, _, hsub, hamb, hmono, _⟩
  exact ⟨paper_real_input_40_reset_word, paper_real_input_40_input_memory_marginal,
    Set.Subset.trans hsub hamb, hmono⟩

end Omega.SyncKernelRealInput
