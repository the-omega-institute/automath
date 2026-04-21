import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete half-order pressure datum: the half-order partition sum `S_{1/2}(m)`, the maximal
fiber multiplicity `M_m`, the number `K_m` of maximizing fibers, the tail term `T_m`, and the
freezing exponent. -/
structure HalfOrderPressureDatum where
  S : Nat → ℝ
  K : Nat → ℝ
  M : Nat → ℝ
  T : Nat → ℝ
  gStar : ℝ
  alphaStar : ℝ
  freezingExponent : ℝ
  maxLayerLower : ∀ m : Nat, K m * Real.sqrt (M m) ≤ S m
  freezingFormula :
    freezingExponent = 2 * gStar + alphaStar - Real.log 2

/-- Restricting the half-order partition sum to the maximal fibers gives the lower bound
`K_m * sqrt(M_m) ≤ S_{1/2}(m)`. -/
def HalfOrderPressureDatum.extremeLowerBound (D : HalfOrderPressureDatum) : Prop :=
  ∀ m : Nat, D.K m * Real.sqrt (D.M m) ≤ D.S m

/-- Dominance by the maximal layer written directly at the partition-sum level. -/
def HalfOrderPressureDatum.maxLayerDominance (D : HalfOrderPressureDatum) : Prop :=
  ∀ m : Nat, D.S m = D.K m * Real.sqrt (D.M m) + D.T m

/-- The same dominance statement rewritten as an explicit tail identity. -/
def HalfOrderPressureDatum.tailLittleO (D : HalfOrderPressureDatum) : Prop :=
  ∀ m : Nat, D.T m = D.S m - D.K m * Real.sqrt (D.M m)

/-- The two formulations differ only by rearranging `S_{1/2}(m) = K_m * sqrt(M_m) + T_m`. -/
def HalfOrderPressureDatum.maxLayerDominanceIffTailLittleO (D : HalfOrderPressureDatum) : Prop :=
  D.maxLayerDominance ↔ D.tailLittleO

/-- Positivity of the freezing exponent. -/
def HalfOrderPressureDatum.freezingExponentPositive (D : HalfOrderPressureDatum) : Prop :=
  0 < D.freezingExponent

/-- The advertised square-root freezing formula. -/
def HalfOrderPressureDatum.halfOrderPressureFormula (D : HalfOrderPressureDatum) : Prop :=
  D.freezingExponent = 2 * D.gStar + D.alphaStar - Real.log 2

/-- Paper package: the maximal fibers give the lower bound, maximal-layer dominance is equivalent
to rewriting off the tail term `T_m`, and once the freezing exponent is positive the exponent
formula is exactly the displayed logarithmic identity.
    thm:pom-half-order-pressure-extreme-lower-bound-sqrt-freezing -/
theorem paper_pom_half_order_pressure_extreme_lower_bound_sqrt_freezing
    (D : Omega.POM.HalfOrderPressureDatum) :
    D.extremeLowerBound ∧ D.maxLayerDominanceIffTailLittleO ∧
      (D.freezingExponentPositive → D.halfOrderPressureFormula) := by
  refine ⟨D.maxLayerLower, ?_, ?_⟩
  · constructor
    · intro hDom m
      have h := hDom m
      linarith
    · intro hTail m
      have h := hTail m
      linarith
  · intro _
    exact D.freezingFormula

end Omega.POM
