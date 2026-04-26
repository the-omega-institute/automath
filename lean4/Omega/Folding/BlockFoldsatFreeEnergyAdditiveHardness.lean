import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.BlockFoldsatNpComplete
import Omega.SPG.PolytimeCompleteInvariantImpliesPEqualsNP

namespace Omega.Folding

/-- Paper label: `cor:block-foldsat-free-energy-additive-hardness`. A uniform additive
approximation with error strictly smaller than half the `log 2` spectral gap lets us threshold the
free energy at `-(log 2) / 2`, recovering the hard predicate and hence the chapter-local
`P = NP` conclusion. -/
theorem paper_block_foldsat_free_energy_additive_hardness
    (D : Omega.Folding.BlockFoldsatNpCompleteData) {Hard : Type} {Family : Type*}
    (hardPred : Hard → Prop) (encode : Hard → Family) (freeEnergy : Family → ℝ)
    (approx : Family → ℝ) (hUnsat : ∀ x, ¬ hardPred x → freeEnergy (encode x) ≤ -Real.log 2)
    (hSat : ∀ x, hardPred x → 0 ≤ freeEnergy (encode x))
    (hApprox : ∀ y, |freeEnergy y - approx y| < Real.log 2 / 2) :
    Omega.SPG.PolytimeDecidable (α := Hard) hardPred ∧
      Omega.SPG.PEqualsNP (Formula := Hard) hardPred := by
  let decideHard : Hard → Bool := fun x => decide (-Real.log 2 / 2 < approx (encode x))
  have _hD : D.npComplete := (paper_block_foldsat_np_complete D).2.2
  have hSpec : ∀ x, decideHard x = true ↔ hardPred x := by
    intro x
    by_cases hx : hardPred x
    · constructor
      · intro _
        exact hx
      · intro _
        have hBounds := abs_lt.mp (hApprox (encode x))
        have hThreshold : -Real.log 2 / 2 < approx (encode x) := by
          have hFree : 0 ≤ freeEnergy (encode x) := hSat x hx
          linarith [Real.log_pos one_lt_two, hBounds.1]
        simpa [decideHard] using hThreshold
    · constructor
      · intro hDecide
        have hBounds := abs_lt.mp (hApprox (encode x))
        have hUpper : approx (encode x) < -Real.log 2 / 2 := by
          have hFree : freeEnergy (encode x) ≤ -Real.log 2 := hUnsat x hx
          linarith [Real.log_pos one_lt_two, hBounds.2]
        have hThreshold : -Real.log 2 / 2 < approx (encode x) := by
          simpa [decideHard] using hDecide
        linarith
      · intro hHard
        exact False.elim (hx hHard)
  have hHard : Omega.SPG.PolytimeDecidable (α := Hard) hardPred := ⟨decideHard, trivial, hSpec⟩
  exact ⟨hHard, ⟨Omega.SPG.complement_polytime_decidable hHard, hHard⟩⟩

end Omega.Folding
