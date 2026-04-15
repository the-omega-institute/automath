import Omega.Folding.YmExactSFTOrder

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for exact Markov order under Bernoulli transport in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    thm:exact-markov-order-bernoulli -/
theorem paper_resolution_folding_exact_markov_order_bernoulli
    (isStepSFT : ℕ → Prop)
    {m : ℕ}
    (hm : 3 ≤ m)
    (bernoulliCylinderLaw nextSymbolKernel mStepMarkov fullSupport noShorterMemory : Prop)
    (hCylinder : bernoulliCylinderLaw)
    (hKernel : bernoulliCylinderLaw → nextSymbolKernel)
    (hMarkov : nextSymbolKernel → mStepMarkov)
    (hmStep : isStepSFT m)
    (hNotPrev : ¬ isStepSFT (m - 1))
    (hSupport : bernoulliCylinderLaw → fullSupport)
    (hMinimal : fullSupport → ¬ isStepSFT (m - 1) → noShorterMemory) :
    nextSymbolKernel ∧ mStepMarkov ∧ noShorterMemory := by
  have hNextSymbolKernel : nextSymbolKernel := hKernel hCylinder
  have hExactStepMarkov : mStepMarkov := hMarkov hNextSymbolKernel
  obtain ⟨_, hNoShorterSFT⟩ :=
    paper_resolution_folding_y_m_exact_sft_order isStepSFT (m := m) hm hmStep hNotPrev
  have hFullSupport : fullSupport := hSupport hCylinder
  exact ⟨hNextSymbolKernel, hExactStepMarkov, hMinimal hFullSupport hNoShorterSFT⟩

end Omega.Folding
