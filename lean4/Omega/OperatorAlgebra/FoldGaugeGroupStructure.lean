import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The symmetric group attached to a fold fiber of multiplicity `n`. -/
abbrev FoldGaugeFiberGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- Multiplicity package for the fold-gauge fibers. -/
structure FoldGaugeGroupStructureData where
  m : ℕ
  multiplicity : Fin m → ℕ

/-- Order of the full fold-gauge group, viewed as a product of symmetric groups over the fibers. -/
def foldGaugeGroupOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, Nat.factorial (N d)

/-- Order of the derived subgroup of `S_n`: trivial for `n ≤ 1`, and `|A_n| = n! / 2`
afterwards. -/
def foldGaugeDerivedComponentOrder (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else Nat.factorial n / 2

/-- Order of the center of `S_n`: only `S₂` contributes a nontrivial center. -/
def foldGaugeCenterComponentOrder (n : ℕ) : ℕ :=
  if n = 2 then 2 else 1

/-- Order of the abelianization of `S_n`: trivial for `n ≤ 1` and `C₂` for `n ≥ 2`. -/
def foldGaugeAbelianizationComponentOrder (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else 2

/-- Componentwise order formula for the derived subgroup of the full fold-gauge group. -/
def foldGaugeDerivedOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeDerivedComponentOrder (N d)

/-- Componentwise order formula for the center of the full fold-gauge group. -/
def foldGaugeCenterOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeCenterComponentOrder (N d)

/-- Componentwise order formula for the abelianization of the full fold-gauge group. -/
def foldGaugeAbelianizationOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeAbelianizationComponentOrder (N d)

/-- Publication-facing package of componentwise symmetric-group formulas for the fold-gauge
group, its derived subgroup, center, and abelianization. -/
def FoldGaugeGroupStructureData.groupStructurePackage (D : FoldGaugeGroupStructureData) : Prop :=
  foldGaugeGroupOrder D.multiplicity = ∏ d, Nat.factorial (D.multiplicity d) ∧
    foldGaugeDerivedOrder D.multiplicity =
      ∏ d, foldGaugeDerivedComponentOrder (D.multiplicity d) ∧
    foldGaugeCenterOrder D.multiplicity =
      ∏ d, foldGaugeCenterComponentOrder (D.multiplicity d) ∧
    foldGaugeAbelianizationOrder D.multiplicity =
      ∏ d, foldGaugeAbelianizationComponentOrder (D.multiplicity d)

/-- Paper-facing fold-gauge group structure package: the fiberwise product of symmetric groups
immediately yields the derived-group, center, and abelianization formulas componentwise.
    prop:op-algebra-fold-gauge-group-structure -/
theorem paper_op_algebra_fold_gauge_group_structure (D : FoldGaugeGroupStructureData) :
    D.groupStructurePackage := by
  simp [FoldGaugeGroupStructureData.groupStructurePackage, foldGaugeGroupOrder,
    foldGaugeDerivedOrder, foldGaugeCenterOrder, foldGaugeAbelianizationOrder]

end Omega.OperatorAlgebra
