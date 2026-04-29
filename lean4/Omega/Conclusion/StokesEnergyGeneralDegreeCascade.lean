import Mathlib
import Omega.Conclusion.StokesEnergyDyadicMartingale

namespace Omega.Conclusion

open scoped BigOperators

/-- Finite coefficient/cell package for the general-degree dyadic Stokes-energy cascade. Each
coefficient on each coarse cell carries the two-child martingale data from the scalar dyadic
energy identity. -/
structure GeneralDegreeStokesEnergyData where
  coeffCount : ℕ
  cellCount : ℕ
  martingale : Fin coeffCount → Fin cellCount → DyadicMartingale

/-- Coarse-scale energy: sum of the parent-cell energies over all coefficients and cells. -/
def coarseEnergyOf (coeffCount cellCount : ℕ)
    (M : Fin coeffCount → Fin cellCount → DyadicMartingale) : ℝ :=
  ∑ i : Fin coeffCount, ∑ Q : Fin cellCount, (M i Q).parent ^ 2

/-- Fine-scale energy: average of the two child energies on each coarse cell. -/
noncomputable def fineEnergyOf (coeffCount cellCount : ℕ)
    (M : Fin coeffCount → Fin cellCount → DyadicMartingale) : ℝ :=
  ∑ i : Fin coeffCount, ∑ Q : Fin cellCount, ((M i Q).left ^ 2 + (M i Q).right ^ 2) / 2

/-- Orthogonal martingale increment summed over all coefficients and cells. -/
noncomputable def cascadeIncrementOf (coeffCount cellCount : ℕ)
    (M : Fin coeffCount → Fin cellCount → DyadicMartingale) : ℝ :=
  ∑ i : Fin coeffCount, ∑ Q : Fin cellCount, ((M i Q).left - (M i Q).right) ^ 2 / 4

/-- Concrete helper theorem: summing the two-child dyadic identity cellwise gives the global
general-degree cascade law and monotonicity. -/
theorem general_degree_stokes_energy_cascade
    (coeffCount cellCount : ℕ) (M : Fin coeffCount → Fin cellCount → DyadicMartingale) :
    fineEnergyOf coeffCount cellCount M =
        coarseEnergyOf coeffCount cellCount M + cascadeIncrementOf coeffCount cellCount M ∧
      (fineEnergyOf coeffCount cellCount M - coarseEnergyOf coeffCount cellCount M =
          cascadeIncrementOf coeffCount cellCount M) ∧
      coarseEnergyOf coeffCount cellCount M ≤ fineEnergyOf coeffCount cellCount M := by
  have hcell :
      ∀ i : Fin coeffCount, ∀ Q : Fin cellCount,
        ((M i Q).left ^ 2 + (M i Q).right ^ 2) / 2 =
          (M i Q).parent ^ 2 + ((M i Q).left - (M i Q).right) ^ 2 / 4 := by
    intro i Q
    have hlocal := (paper_conclusion_stokes_energy_dyadic_martingale (M i Q)).2.2
    dsimp [Omega.Conclusion.incrementFormula] at hlocal
    nlinarith
  have hEnergy :
      fineEnergyOf coeffCount cellCount M =
        coarseEnergyOf coeffCount cellCount M + cascadeIncrementOf coeffCount cellCount M := by
    unfold fineEnergyOf coarseEnergyOf cascadeIncrementOf
    calc
      ∑ i : Fin coeffCount, ∑ Q : Fin cellCount, ((M i Q).left ^ 2 + (M i Q).right ^ 2) / 2
          = ∑ i : Fin coeffCount,
              ∑ Q : Fin cellCount,
                ((M i Q).parent ^ 2 + ((M i Q).left - (M i Q).right) ^ 2 / 4) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro Q _
              exact hcell i Q
      _ = ∑ i : Fin coeffCount,
            ((∑ Q : Fin cellCount, (M i Q).parent ^ 2) +
              ∑ Q : Fin cellCount, ((M i Q).left - (M i Q).right) ^ 2 / 4) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin coeffCount, ∑ Q : Fin cellCount, (M i Q).parent ^ 2) +
            ∑ i : Fin coeffCount, ∑ Q : Fin cellCount, ((M i Q).left - (M i Q).right) ^ 2 / 4 := by
            rw [Finset.sum_add_distrib]
      _ = coarseEnergyOf coeffCount cellCount M + cascadeIncrementOf coeffCount cellCount M := by
            rfl
  have hNonneg : 0 ≤ cascadeIncrementOf coeffCount cellCount M := by
    unfold cascadeIncrementOf
    refine Finset.sum_nonneg ?_
    intro i _
    refine Finset.sum_nonneg ?_
    intro Q _
    positivity
  refine ⟨hEnergy, ?_, ?_⟩
  · nlinarith [hEnergy]
  · nlinarith [hEnergy, hNonneg]

/-- The global coarse/fine energy identity for a finite general-degree dyadic package. -/
def GeneralDegreeStokesEnergyData.energyFormula (D : GeneralDegreeStokesEnergyData) : Prop :=
  fineEnergyOf D.coeffCount D.cellCount D.martingale =
    coarseEnergyOf D.coeffCount D.cellCount D.martingale +
      cascadeIncrementOf D.coeffCount D.cellCount D.martingale

/-- The global increment formula recording the orthogonal energy gain from one dyadic refinement. -/
def GeneralDegreeStokesEnergyData.incrementFormula (D : GeneralDegreeStokesEnergyData) : Prop :=
  fineEnergyOf D.coeffCount D.cellCount D.martingale -
      coarseEnergyOf D.coeffCount D.cellCount D.martingale =
    cascadeIncrementOf D.coeffCount D.cellCount D.martingale

/-- Monotonicity of the dyadic Stokes energy along refinement. -/
def GeneralDegreeStokesEnergyData.monotone (D : GeneralDegreeStokesEnergyData) : Prop :=
  coarseEnergyOf D.coeffCount D.cellCount D.martingale ≤
    fineEnergyOf D.coeffCount D.cellCount D.martingale

/-- Paper label: `thm:conclusion-stokes-energy-general-degree-cascade`. Package the finite
coefficient/cellwise dyadic identities into the global energy formula, the explicit increment
formula, and monotonicity. -/
theorem paper_conclusion_stokes_energy_general_degree_cascade
    (D : GeneralDegreeStokesEnergyData) :
    D.energyFormula ∧ D.incrementFormula ∧ D.monotone := by
  simpa [GeneralDegreeStokesEnergyData.energyFormula,
    GeneralDegreeStokesEnergyData.incrementFormula, GeneralDegreeStokesEnergyData.monotone] using
    general_degree_stokes_energy_cascade D.coeffCount D.cellCount D.martingale

end Omega.Conclusion
