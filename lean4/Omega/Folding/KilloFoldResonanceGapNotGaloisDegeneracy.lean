import Omega.Folding.KilloFoldResonanceGapSimpleModule

namespace Omega.Folding

/-- Paper label: `cor:killo-fold-resonance-gap-not-galois-degeneracy`. -/
theorem paper_killo_fold_resonance_gap_not_galois_degeneracy
    (fullGalois : ℕ → Prop)
    (hGap :
      ∀ q ∈ ({13, 14, 15, 16, 17} : Finset ℕ),
        0 < killo_fold_resonance_gap_simple_module_delta q)
    (hGal : ∀ q ∈ ({13, 14, 15, 16, 17} : Finset ℕ), fullGalois q) :
    ∀ q ∈ ({13, 14, 15, 16, 17} : Finset ℕ),
      0 < killo_fold_resonance_gap_simple_module_delta q ∧ fullGalois q := by
  intro q hq
  exact ⟨hGap q hq, hGal q hq⟩

end Omega.Folding
