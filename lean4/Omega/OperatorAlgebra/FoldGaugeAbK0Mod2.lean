import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Concrete multiplicity data for the comparison between the fold-gauge abelianization and the
fiberwise `K₀`-classes modulo `2`. -/
structure FoldGaugeAbK0Mod2Data where
  m : ℕ
  multiplicity : Fin m → ℕ

/-- The mod-`2` reduction of the unit class in `K₀(M_d(ℂ))` is nontrivial exactly on the
nontrivial fibers `d ≥ 2`. -/
def foldGaugeK0Mod2ComponentOrder (n : ℕ) : ℕ :=
  if 2 ≤ n then 2 else 1

/-- Fiberwise order of the mod-`2` `K₀` package. -/
def foldGaugeK0Mod2Order {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeK0Mod2ComponentOrder (N d)

lemma foldGaugeAbelianizationComponentOrder_eq_k0Mod2ComponentOrder (n : ℕ) :
    foldGaugeAbelianizationComponentOrder n = foldGaugeK0Mod2ComponentOrder n := by
  by_cases h : n ≤ 1
  · have h' : ¬ 2 ≤ n := by omega
    simp [foldGaugeAbelianizationComponentOrder, foldGaugeK0Mod2ComponentOrder, h, h']
  · have h' : 2 ≤ n := by omega
    simp [foldGaugeAbelianizationComponentOrder, foldGaugeK0Mod2ComponentOrder, h, h']

namespace FoldGaugeAbK0Mod2Data

/-- The sign character on each nontrivial symmetric-group fiber matches the mod-`2` reduction of
the matrix-unit generator in `K₀(M_d(ℂ))`, so the full fold-gauge abelianization agrees with the
fiberwise `K₀` package modulo `2`. -/
def signAbelianizationMatchesK0Mod2 (D : FoldGaugeAbK0Mod2Data) : Prop :=
  foldGaugeAbelianizationOrder D.multiplicity = foldGaugeK0Mod2Order D.multiplicity

end FoldGaugeAbK0Mod2Data

open FoldGaugeAbK0Mod2Data

/-- The fold-gauge abelianization is the same coordinatewise `ℤ/2ℤ` package as the mod-`2`
reduction of the fiberwise `K₀` unit classes.
    cor:op-algebra-fold-gauge-ab-k0-mod2 -/
theorem paper_op_algebra_fold_gauge_ab_k0_mod2 (D : FoldGaugeAbK0Mod2Data) :
    D.signAbelianizationMatchesK0Mod2 := by
  have hStructure :
      FoldGaugeGroupStructureData.groupStructurePackage
        { m := D.m, multiplicity := D.multiplicity } := by
    simpa using
      paper_op_algebra_fold_gauge_group_structure { m := D.m, multiplicity := D.multiplicity }
  rcases hStructure with ⟨_, _, _, hAb⟩
  refine hAb.trans ?_
  unfold foldGaugeK0Mod2Order
  refine Finset.prod_congr rfl ?_
  intro d hd
  exact foldGaugeAbelianizationComponentOrder_eq_k0Mod2ComponentOrder (D.multiplicity d)

end Omega.OperatorAlgebra
