import Mathlib.Tactic
import Omega.Conclusion.FoldWalshGramSimplexSignatureSection

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

local instance (m : ℕ) : DecidableEq (Word m) :=
  Classical.decEq _

local instance (m : ℕ) : DecidableEq (X m) :=
  Classical.decEq _

/-- Summing the empty Walsh coefficient over all fibers recovers the total charge `2^m`. -/
def foldWalshTotalChargeConservation (m : ℕ) : Prop :=
  ∑ x : X m, walshProfile m x ∅ = (2 : ℝ) ^ m

/-- Parseval on a single fiber recovers its cardinality from the full Walsh spectrum. -/
def foldWalshFiberCardinalityParseval (m : ℕ) : Prop :=
  ∀ x : X m, ∑ I ∈ allSubsets m, walshProfile m x I ^ 2 = (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ)

/-- Summing the fiberwise Parseval laws yields the total `4^m` Walsh energy. -/
def foldWalshTotalEnergy (m : ℕ) : Prop :=
  ∑ x : X m, ∑ I ∈ allSubsets m, walshProfile m x I ^ 2 = (4 : ℝ) ^ m

/-- The total-charge law comes from summing the empty Walsh mode over fibers; Parseval then
recovers each fiber cardinality, and summing over fibers gives the exact `4^m` total energy.
    thm:conclusion-fold-walsh-total-charge-parseval-degeneracy -/
theorem paper_conclusion_fold_walsh_total_charge_parseval_degeneracy (m : ℕ) :
    foldWalshTotalChargeConservation m ∧
      foldWalshFiberCardinalityParseval m ∧
      foldWalshTotalEnergy m := by
  have hcharge : foldWalshTotalChargeConservation m := by
    dsimp [foldWalshTotalChargeConservation]
    simpa [walshProfile_empty] using
      (show ∑ x : X m, (X.fiberMultiplicity x : ℝ) = (2 : ℝ) ^ m by
        exact_mod_cast X.fiberMultiplicity_sum_eq_pow m)
  have hparseval : foldWalshFiberCardinalityParseval m := by
    intro x
    let F : Finset (Fin m) → ℝ := fun I => walshProfile m x I ^ 2
    have hsplit :
        ∑ I ∈ allSubsets m, F I = ∑ I ∈ nonemptySubsets m, F I + F ∅ := by
      simpa [allSubsets, nonemptySubsets, F, add_comm] using
        (Finset.sum_erase_add (s := allSubsets m) (f := F) (a := ∅) (by simp))
    have hgram :
        ∑ I ∈ nonemptySubsets m, F I =
          (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) -
            (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity x : ℝ) := by
      simpa [F, pow_two] using paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x x
    have hempty :
        F ∅ = (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity x : ℝ) := by
      simp [F, walshProfile_empty, pow_two]
    linarith
  have henergy : foldWalshTotalEnergy m := by
    have hsum :
        ∑ x : X m, (X.fiberMultiplicity x : ℝ) = (2 : ℝ) ^ m := by
      exact_mod_cast X.fiberMultiplicity_sum_eq_pow m
    dsimp [foldWalshTotalEnergy]
    calc
      ∑ x : X m, ∑ I ∈ allSubsets m, walshProfile m x I ^ 2
          = ∑ x : X m, (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact hparseval x
      _ = (2 : ℝ) ^ m * ∑ x : X m, (X.fiberMultiplicity x : ℝ) := by
            rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ m * (2 : ℝ) ^ m := by rw [hsum]
      _ = (4 : ℝ) ^ m := by
            rw [← mul_pow]
            norm_num
  exact ⟨hcharge, hparseval, henergy⟩

end

end Omega.Conclusion
