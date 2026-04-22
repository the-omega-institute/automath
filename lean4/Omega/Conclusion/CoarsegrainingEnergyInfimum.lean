import Mathlib
import Omega.Conclusion.CoarsegrainingStokesBeckChevalley

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete finite-fiber coarse-graining data for the quadratic energy comparison. Each coarse
edge `e` carries a finite fiber of microscopic cross-edges indexed by `Fin (fiberCard e)` with
weights `weight e i`, and `coarseCurrent e` is the prescribed coarse current on that block. -/
structure ConclusionCoarsegrainingEnergyInfimumData where
  Ebar : Type
  [fintypeEbar : Fintype Ebar]
  [decidableEqEbar : DecidableEq Ebar]
  fiberCard : Ebar → ℕ
  weight : (e : Ebar) → Fin (fiberCard e) → ℝ
  coarseCurrent : Ebar → ℝ
  weight_nonneg : ∀ e i, 0 ≤ weight e i

attribute [instance] ConclusionCoarsegrainingEnergyInfimumData.fintypeEbar
attribute [instance] ConclusionCoarsegrainingEnergyInfimumData.decidableEqEbar

namespace ConclusionCoarsegrainingEnergyInfimumData

/-- The total coarse conductance on a coarse edge is the sum of the microscopic conductances in
its fiber. -/
def coarseWeight (D : ConclusionCoarsegrainingEnergyInfimumData) (e : D.Ebar) : ℝ :=
  ∑ i : Fin (D.fiberCard e), D.weight e i

/-- The microscopic energy of a current profile `J`. -/
def fineEnergyOf (D : ConclusionCoarsegrainingEnergyInfimumData)
    (J : (e : D.Ebar) → Fin (D.fiberCard e) → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ e : D.Ebar, ∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ)

/-- The coarse energy obtained after summing the microscopic weights fiberwise. -/
def coarseEnergy (D : ConclusionCoarsegrainingEnergyInfimumData) : ℝ :=
  (1 / 2 : ℝ) * ∑ e : D.Ebar, D.coarseWeight e * (D.coarseCurrent e) ^ (2 : ℕ)

/-- The microscopic current profiles whose weighted pushforward agrees with the coarse current on
every coarse-edge fiber. -/
def pushforwardCompatible (D : ConclusionCoarsegrainingEnergyInfimumData)
    (J : (e : D.Ebar) → Fin (D.fiberCard e) → ℝ) : Prop :=
  ∀ e : D.Ebar,
    (∑ i : Fin (D.fiberCard e), D.weight e i * J e i) = D.coarseWeight e * D.coarseCurrent e

/-- The unique minimizer in the exact coarse-graining model is constant on each coarse-edge
fiber. -/
def minimizer (D : ConclusionCoarsegrainingEnergyInfimumData) :
    (e : D.Ebar) → Fin (D.fiberCard e) → ℝ :=
  fun e _i => D.coarseCurrent e

/-- The infimal energy is realized by the fiberwise-constant minimizer. -/
def infimumEnergy (D : ConclusionCoarsegrainingEnergyInfimumData) : ℝ :=
  D.fineEnergyOf D.minimizer

lemma minimizer_pushforward (D : ConclusionCoarsegrainingEnergyInfimumData) :
    D.pushforwardCompatible D.minimizer := by
  intro e
  change ∑ i : Fin (D.fiberCard e), D.weight e i * D.coarseCurrent e =
      D.coarseWeight e * D.coarseCurrent e
  calc
    ∑ i : Fin (D.fiberCard e), D.weight e i * D.coarseCurrent e =
        ∑ i : Fin (D.fiberCard e), D.coarseCurrent e * D.weight e i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = D.coarseCurrent e * ∑ i : Fin (D.fiberCard e), D.weight e i := by
          rw [Finset.mul_sum]
    _ = D.coarseWeight e * D.coarseCurrent e := by
          rw [coarseWeight]
          ring

private lemma block_square_gap (D : ConclusionCoarsegrainingEnergyInfimumData)
    (J : (e : D.Ebar) → Fin (D.fiberCard e) → ℝ)
    (e : D.Ebar) :
    0 ≤ ∑ i : Fin (D.fiberCard e), D.weight e i * (J e i - D.coarseCurrent e) ^ (2 : ℕ) := by
  refine Finset.sum_nonneg ?_
  intro i hi
  have hw : 0 ≤ D.weight e i := D.weight_nonneg e i
  positivity

lemma block_lower_bound (D : ConclusionCoarsegrainingEnergyInfimumData)
    (J : (e : D.Ebar) → Fin (D.fiberCard e) → ℝ)
    (hJ : D.pushforwardCompatible J) (e : D.Ebar) :
    D.coarseWeight e * (D.coarseCurrent e) ^ (2 : ℕ) ≤
      ∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ) := by
  have hgap := D.block_square_gap J e
  have hpush := hJ e
  have hidentity :
      ∑ i : Fin (D.fiberCard e), D.weight e i * (J e i - D.coarseCurrent e) ^ (2 : ℕ) =
        (∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ)) -
          D.coarseWeight e * (D.coarseCurrent e) ^ (2 : ℕ) := by
    calc
      ∑ i : Fin (D.fiberCard e), D.weight e i * (J e i - D.coarseCurrent e) ^ (2 : ℕ) =
          ∑ i : Fin (D.fiberCard e),
            (D.weight e i * (J e i) ^ (2 : ℕ) -
              (2 * D.coarseCurrent e) * (D.weight e i * J e i) +
              D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ =
          (∑ i : Fin (D.fiberCard e),
              (D.weight e i * (J e i) ^ (2 : ℕ) -
                (2 * D.coarseCurrent e) * (D.weight e i * J e i))) +
            ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ)) -
            ∑ i : Fin (D.fiberCard e), (2 * D.coarseCurrent e) * (D.weight e i * J e i) +
            ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) := by
            rw [Finset.sum_sub_distrib]
      _ =
          (∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ)) -
            (2 * D.coarseCurrent e) *
              (∑ i : Fin (D.fiberCard e), D.weight e i * J e i) +
            ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) := by
            rw [← Finset.mul_sum]
      _ =
          (∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ)) -
            (2 * D.coarseCurrent e) * (D.coarseWeight e * D.coarseCurrent e) +
            ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) := by
            rw [hpush]
      _ =
          (∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ)) -
            D.coarseWeight e * (D.coarseCurrent e) ^ (2 : ℕ) := by
            rw [coarseWeight]
            have hconst :
                ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) =
                  (∑ i : Fin (D.fiberCard e), D.weight e i) * (D.coarseCurrent e) ^ (2 : ℕ) := by
              calc
                ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) =
                    ∑ i : Fin (D.fiberCard e), (D.coarseCurrent e) ^ (2 : ℕ) * D.weight e i := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
                _ = (D.coarseCurrent e) ^ (2 : ℕ) *
                      ∑ i : Fin (D.fiberCard e), D.weight e i := by
                      rw [Finset.mul_sum]
                _ = (∑ i : Fin (D.fiberCard e), D.weight e i) * (D.coarseCurrent e) ^ (2 : ℕ) := by
                      ring
            rw [hconst]
            ring
  linarith

lemma fineEnergy_lower_bound (D : ConclusionCoarsegrainingEnergyInfimumData)
    (J : (e : D.Ebar) → Fin (D.fiberCard e) → ℝ) (hJ : D.pushforwardCompatible J) :
    D.coarseEnergy ≤ D.fineEnergyOf J := by
  unfold coarseEnergy fineEnergyOf
  have hsum :
      ∑ e : D.Ebar, D.coarseWeight e * (D.coarseCurrent e) ^ (2 : ℕ) ≤
        ∑ e : D.Ebar, ∑ i : Fin (D.fiberCard e), D.weight e i * (J e i) ^ (2 : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro e he
    exact D.block_lower_bound J hJ e
  nlinarith

lemma minimizer_energy_eq_coarseEnergy (D : ConclusionCoarsegrainingEnergyInfimumData) :
    D.fineEnergyOf D.minimizer = D.coarseEnergy := by
  unfold fineEnergyOf coarseEnergy minimizer coarseWeight
  congr 1
  refine Finset.sum_congr rfl ?_
  intro e he
  calc
    ∑ i : Fin (D.fiberCard e), D.weight e i * (D.coarseCurrent e) ^ (2 : ℕ) =
        ∑ i : Fin (D.fiberCard e), (D.coarseCurrent e) ^ (2 : ℕ) * D.weight e i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = (D.coarseCurrent e) ^ (2 : ℕ) * ∑ i : Fin (D.fiberCard e), D.weight e i := by
          rw [Finset.mul_sum]
    _ = (∑ i : Fin (D.fiberCard e), D.weight e i) * (D.coarseCurrent e) ^ (2 : ℕ) := by
          ring

end ConclusionCoarsegrainingEnergyInfimumData

open ConclusionCoarsegrainingEnergyInfimumData

/-- Paper label: `prop:conclusion-coarsegraining-energy-infimum`.
The coarse energy is the exact microscopic infimum for the fiberwise-constant minimizer. -/
theorem paper_conclusion_coarsegraining_energy_infimum
    (D : ConclusionCoarsegrainingEnergyInfimumData) : D.infimumEnergy = D.coarseEnergy := by
  simpa [ConclusionCoarsegrainingEnergyInfimumData.infimumEnergy] using
    D.minimizer_energy_eq_coarseEnergy

end

end Omega.Conclusion
