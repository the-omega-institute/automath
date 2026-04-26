import Omega.SyncKernelRealInput.GmSmithComputeObstructions
import Omega.SyncKernelRealInput.GMImprovabilityIffD1

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:gm-two-finite-objects-outline`. -/
theorem paper_gm_two_finite_objects_outline (cycleWeights : List ℤ) :
    ∃ d : ℕ, d = cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0 ∧
      (∀ z ∈ cycleWeights, d ∣ z.natAbs) ∧
        (d = 1 ↔
          Omega.SyncKernelRealInput.gm_improvability_iff_d1_analytically_improvable d) := by
  rcases paper_gm_smith_compute_obstructions cycleWeights with ⟨d, hd, hdvd⟩
  refine ⟨d, hd, hdvd, ?_⟩
  exact (paper_gm_improvability_iff_d1 d).symm

end Omega.SyncKernelRealInput
