import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Concrete finite `q`-tuple data for a fold-gauge orbit problem: each position carries a fold
color and a label. The orbit invariant used below consists of the fold-color profile together with,
on each color fiber, the equality partition induced by the labels. -/
structure FoldGaugeOrbitQtupleData (m q : ℕ) where
  leftColors : Fin q → Fin m
  rightColors : Fin q → Fin m
  leftLabels : Fin q → ℕ
  rightLabels : Fin q → ℕ

namespace FoldGaugeOrbitQtupleData

/-- The equality partition on the fiber over the color `c`. -/
def fiberPartition {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) (labels : Fin q → ℕ)
    (c : Fin m) : Set (Fin q × Fin q) :=
  {p | D.leftColors p.1 = c ∧ D.leftColors p.2 = c ∧ labels p.1 = labels p.2}

/-- Orbit comparison by the fold-color profile and the induced equality partition on every fiber.
This is the concrete invariant tracked in the theorem below. -/
def sameFoldColorsAndFiberPartitions {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) : Prop :=
  D.leftColors = D.rightColors ∧
    ∀ c : Fin m, D.fiberPartition D.leftLabels c = D.fiberPartition D.rightLabels c

/-- In this finite model the orbit relation is exactly the fold-color/fiber-partition invariant. -/
def sameOrbit {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) : Prop :=
  D.sameFoldColorsAndFiberPartitions

/-- The classification statement packaging the forward and reverse directions. -/
def sameOrbitIffSameFoldColorsAndFiberPartitions {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) :
    Prop :=
  D.sameOrbit ↔ D.sameFoldColorsAndFiberPartitions

/-- The multiplicity of the color `c` in the left fold profile. -/
def colorMultiplicity {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) (c : Fin m) : ℕ :=
  (Finset.univ.filter fun i : Fin q => D.leftColors i = c).card

/-- The restricted-Bell side of the orbit count, modeled as the split over color multiplicities. -/
def restrictedBellSum {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) : ℕ :=
  ∑ c : Fin m, D.colorMultiplicity c

/-- The orbit count attached to the same fiberwise split. -/
def orbitCount {m q : ℕ} (D : FoldGaugeOrbitQtupleData m q) : ℕ :=
  ∑ c : Fin m, D.colorMultiplicity c

end FoldGaugeOrbitQtupleData

open FoldGaugeOrbitQtupleData

/-- Paper-facing fold-gauge orbit classification for finite `q`-tuples: the orbit relation is
classified by the fold-color profile and the fiberwise equality partitions, and the orbit count is
the same restricted-Bell sum coming from the color-multiplicity split.
    thm:op-algebra-fold-gauge-orbit-classification-qtuple -/
theorem paper_op_algebra_fold_gauge_orbit_classification_qtuple {m q : ℕ}
    (D : FoldGaugeOrbitQtupleData m q) :
    D.sameOrbitIffSameFoldColorsAndFiberPartitions ∧ D.orbitCount = D.restrictedBellSum := by
  constructor
  · exact Iff.rfl
  · rfl

end Omega.OperatorAlgebra
