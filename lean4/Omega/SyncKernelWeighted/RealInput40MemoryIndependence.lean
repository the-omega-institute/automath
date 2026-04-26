import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40InputMemoryMarginal

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `cor:real-input-40-memory-independence`. The one-bit marginal computed from the
four memory-state masses satisfies `P(11) = P(p_x = 1) P(p_y = 1)`. -/
theorem paper_real_input_40_memory_independence :
    realInput40InputOneDensity = (5 - Real.sqrt 5) / 10 ∧
      realInput40Memory11 = realInput40InputOneDensity * realInput40InputOneDensity := by
  rcases paper_real_input_40_input_memory_marginal with
    ⟨_, _, _, h11, hone, _, _, _, _⟩
  refine ⟨hone, ?_⟩
  rw [hone, h11]
  have hs : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith

end

end Omega.SyncKernelWeighted
