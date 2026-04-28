import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40BFKTheory
import Omega.SyncKernelWeighted.RealInput40NilpotentIndex

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-bf-jordan-tower-separation`. The stable
Bowen--Franks and Cuntz--Krieger invariants are trivial while the full and essential
zero-spectrum Jordan towers separate strictly at the audited depths. -/
theorem paper_conclusion_realinput40_bf_jordan_tower_separation :
    Omega.SyncKernelWeighted.realInput40BowenFranksOrder = 1 ∧
      Omega.SyncKernelWeighted.realInput40CuntzKriegerK0Rank = 0 ∧
      Omega.SyncKernelWeighted.realInput40CuntzKriegerK1Rank = 0 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_essential_kernel_dim 3 = 11 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim 4 ≠ 31 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim 5 = 31 := by
  rcases Omega.SyncKernelWeighted.paper_real_input_40_bf_ktheory with
    ⟨_, _, _, _, hBF, hK0, hK1⟩
  rcases Omega.SyncKernelWeighted.paper_real_input_40_nilpotent_index with
    ⟨_, _, hEssential3, _, _, _, _, hFull4, hFull5, _⟩
  refine ⟨hBF, hK0, hK1, hEssential3, ?_, hFull5⟩
  intro h
  rw [hFull4] at h
  omega

end Omega.Conclusion
