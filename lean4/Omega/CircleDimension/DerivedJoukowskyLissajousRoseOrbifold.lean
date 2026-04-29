import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The Joukowsky phase restricted to the unit circle coordinate `e^{it}`. -/
noncomputable def joukowskyPhase (t : ℝ) : ℝ :=
  Real.cos t

/-- Arithmetic shadow of the statement that the `π`-fibers are Klein-four orbits. -/
def joukowskyPiFibersAreKOrbits : Prop :=
  ∀ t : ℝ, joukowskyPhase (-t) = joukowskyPhase t

/-- The planar Lissajous parameterization obtained from the two Joukowsky coordinates. -/
noncomputable def lissajousPoint (a b : Nat) (t : ℝ) : ℝ × ℝ :=
  (Real.cos ((a : ℝ) * t), Real.cos ((b : ℝ) * t))

/-- The Lissajous pair factors through the quotient by sign reversal. -/
def lissajousFactorsThroughQuotient (a b : Nat) : Prop :=
  ∀ t : ℝ, lissajousPoint a b (-t) = lissajousPoint a b t

/-- Product-to-sum form of the rational-rose Laurent lift. -/
def rationalRoseLaurentLift (a b : Nat) : Prop :=
  ∀ t : ℝ,
    Real.cos (((a : ℝ) + b) * t) + Real.cos (((a : ℝ) - b) * t) =
      2 * Real.cos ((a : ℝ) * t) * Real.cos ((b : ℝ) * t)

/-- Paper label: `thm:derived-joukowsky-lissajous-rose-orbifold`. -/
theorem paper_derived_joukowsky_lissajous_rose_orbifold (a b : Nat) :
    joukowskyPiFibersAreKOrbits ∧
      lissajousFactorsThroughQuotient a b ∧
      rationalRoseLaurentLift a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simp [joukowskyPhase]
  · intro t
    ext <;>
    simp [lissajousPoint, Real.cos_neg, mul_comm]
  · intro t
    have hadd : ((a : ℝ) + b) * t = (a : ℝ) * t + (b : ℝ) * t := by ring
    have hsub : ((a : ℝ) - b) * t = (a : ℝ) * t - (b : ℝ) * t := by ring
    rw [hadd, hsub, Real.cos_add, Real.cos_sub]
    ring

end Omega.CircleDimension
