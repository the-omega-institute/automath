import Omega.Folding.FoldbinSaturationSectorThreshold

namespace Omega.Folding

/-- Paper label: `thm:xi-foldbin-fiberwise-saturation-sector-criterion`. -/
theorem paper_xi_foldbin_fiberwise_saturation_sector_criterion (m : ℕ) (hm : 2 ≤ m) :
    (∀ w : Omega.X m, Omega.Folding.foldbinSaturatesUpperBound m w ↔
      Omega.get w.1 (m - 1) = false ∧
        Omega.stableValue w + Omega.Folding.foldbinSMax m ≤ 2 ^ m - 1) ∧
    (∀ w : Omega.X m, Omega.get w.1 (m - 1) = true →
      ¬ Omega.Folding.foldbinSaturatesUpperBound m w) ∧
    (∀ w : Omega.X m, 2 ^ m - 1 < Omega.stableValue w + Omega.Folding.foldbinSMax m →
      ¬ Omega.Folding.foldbinSaturatesUpperBound m w) := by
  rcases paper_foldbin_saturation_sector_threshold m hm with ⟨hthreshold, _, hlast, hslack⟩
  exact ⟨hthreshold, hlast, hslack⟩

end Omega.Folding
