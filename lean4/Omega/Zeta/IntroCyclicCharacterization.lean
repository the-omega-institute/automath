import Omega.Zeta.CyclicFredholmRealization

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the introduction-level cyclic-block
    characterization theorem in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    thm:intro-cyclic-characterization -/
theorem paper_fredholm_witt_intro_cyclic_characterization
    (cyclicBlockRealization normalRealization dimensionOptimality : Prop)
    (hRealization : cyclicBlockRealization)
    (hCharacterization : cyclicBlockRealization ↔ normalRealization)
    (hOptimality : normalRealization → dimensionOptimality) :
    cyclicBlockRealization ∧
      normalRealization ∧
      dimensionOptimality := by
  exact paper_fredholm_witt_cyclic_block_characterization
    cyclicBlockRealization normalRealization dimensionOptimality
    hRealization hCharacterization hOptimality

end Omega.Zeta
