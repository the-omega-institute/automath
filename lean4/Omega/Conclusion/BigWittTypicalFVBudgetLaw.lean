import Mathlib.Tactic
import Omega.Conclusion.BigWittExactSpectralBudget

namespace Omega.Conclusion

/-- Label-prefixed Frobenius transform on the finite Big-Witt atom list. For `p`-typical input,
each block length is divided by `p` and the multiplicity records the `p` resulting blocks. -/
def conclusion_bigwitt_typical_fv_budget_law_frobenius
    (p : ℕ) (D : List BigWittAtom) : List BigWittAtom :=
  D.map fun A =>
    { weight := A.weight
      cycleLength := A.cycleLength / p
      multiplicity := p * A.multiplicity }

/-- Label-prefixed Verschiebung transform on the finite Big-Witt atom list. -/
def conclusion_bigwitt_typical_fv_budget_law_verschiebung
    (p : ℕ) (D : List BigWittAtom) : List BigWittAtom :=
  D.map fun A =>
    { weight := A.weight
      cycleLength := p * A.cycleLength
      multiplicity := A.multiplicity }

/-- Paper label: `cor:conclusion-bigwitt-typical-fv-budget-law`. In the list model, Frobenius
preserves the spectral budget on `p`-typical blocks, while Verschiebung multiplies it by `p`. -/
theorem paper_conclusion_bigwitt_typical_fv_budget_law (p : ℕ) (hp : 0 < p)
    (D : List BigWittAtom) (hD : ∀ A ∈ D, p ∣ A.cycleLength) :
    bigWittSpectralBudget (conclusion_bigwitt_typical_fv_budget_law_frobenius p D) =
        bigWittSpectralBudget D ∧
      bigWittSpectralBudget (conclusion_bigwitt_typical_fv_budget_law_verschiebung p D) =
        p * bigWittSpectralBudget D ∧
      bigWittSpectralBudget
          (conclusion_bigwitt_typical_fv_budget_law_frobenius p
            (conclusion_bigwitt_typical_fv_budget_law_verschiebung p D)) =
        p * bigWittSpectralBudget D := by
  induction D with
  | nil =>
      simp [bigWittSpectralBudget, conclusion_bigwitt_typical_fv_budget_law_frobenius,
        conclusion_bigwitt_typical_fv_budget_law_verschiebung]
  | cons A D ih =>
      have hA : p ∣ A.cycleLength := hD A (by simp)
      have hD_tail : ∀ B ∈ D, p ∣ B.cycleLength := by
        intro B hB
        exact hD B (by simp [hB])
      rcases ih hD_tail with ⟨ihF, ihV, ihFV⟩
      have hF_atom :
          bigWittAtomBudget
              ({ weight := A.weight
                 cycleLength := A.cycleLength / p
                 multiplicity := p * A.multiplicity } : BigWittAtom) =
            bigWittAtomBudget A := by
        change (p * A.multiplicity) * (A.cycleLength / p) =
          A.multiplicity * A.cycleLength
        calc
          (p * A.multiplicity) * (A.cycleLength / p)
              = A.multiplicity * (p * (A.cycleLength / p)) := by ac_rfl
          _ = A.multiplicity * A.cycleLength := by rw [Nat.mul_div_cancel' hA]
      have hV_atom :
          bigWittAtomBudget
              ({ weight := A.weight
                 cycleLength := p * A.cycleLength
                 multiplicity := A.multiplicity } : BigWittAtom) =
            p * bigWittAtomBudget A := by
        simp [bigWittAtomBudget]
        ac_rfl
      have hFV_atom :
          bigWittAtomBudget
              ({ weight := A.weight
                 cycleLength := (p * A.cycleLength) / p
                 multiplicity := p * A.multiplicity } : BigWittAtom) =
            p * bigWittAtomBudget A := by
        simp [bigWittAtomBudget, Nat.mul_div_right _ hp]
        ac_rfl
      refine ⟨?_, ?_, ?_⟩
      · calc
          bigWittSpectralBudget
              (conclusion_bigwitt_typical_fv_budget_law_frobenius p (A :: D))
              =
            bigWittAtomBudget
                ({ weight := A.weight
                   cycleLength := A.cycleLength / p
                   multiplicity := p * A.multiplicity } : BigWittAtom) +
              bigWittSpectralBudget
                (conclusion_bigwitt_typical_fv_budget_law_frobenius p D) := by
              simp [bigWittSpectralBudget, conclusion_bigwitt_typical_fv_budget_law_frobenius]
          _ = bigWittAtomBudget A + bigWittSpectralBudget D := by rw [hF_atom, ihF]
          _ = bigWittSpectralBudget (A :: D) := by simp [bigWittSpectralBudget]
      · calc
          bigWittSpectralBudget
              (conclusion_bigwitt_typical_fv_budget_law_verschiebung p (A :: D))
              =
            bigWittAtomBudget
                ({ weight := A.weight
                   cycleLength := p * A.cycleLength
                   multiplicity := A.multiplicity } : BigWittAtom) +
              bigWittSpectralBudget
                (conclusion_bigwitt_typical_fv_budget_law_verschiebung p D) := by
              simp [bigWittSpectralBudget,
                conclusion_bigwitt_typical_fv_budget_law_verschiebung]
          _ = p * bigWittAtomBudget A + p * bigWittSpectralBudget D := by rw [hV_atom, ihV]
          _ = p * (bigWittAtomBudget A + bigWittSpectralBudget D) := by
              rw [Nat.left_distrib]
          _ = p * bigWittSpectralBudget (A :: D) := by simp [bigWittSpectralBudget]
      · calc
          bigWittSpectralBudget
              (conclusion_bigwitt_typical_fv_budget_law_frobenius p
                (conclusion_bigwitt_typical_fv_budget_law_verschiebung p (A :: D)))
              =
            bigWittAtomBudget
                ({ weight := A.weight
                   cycleLength := (p * A.cycleLength) / p
                   multiplicity := p * A.multiplicity } : BigWittAtom) +
              bigWittSpectralBudget
                (conclusion_bigwitt_typical_fv_budget_law_frobenius p
                  (conclusion_bigwitt_typical_fv_budget_law_verschiebung p D)) := by
              simp [bigWittSpectralBudget, conclusion_bigwitt_typical_fv_budget_law_frobenius,
                conclusion_bigwitt_typical_fv_budget_law_verschiebung]
          _ = p * bigWittAtomBudget A + p * bigWittSpectralBudget D := by
              rw [hFV_atom, ihFV]
          _ = p * (bigWittAtomBudget A + bigWittSpectralBudget D) := by
              rw [Nat.left_distrib]
          _ = p * bigWittSpectralBudget (A :: D) := by simp [bigWittSpectralBudget]

end Omega.Conclusion
