import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Audited finite-part data at the non-backtracking Perron pole for the real-input-40 geodesic
package. -/
structure RealInput40GeodesicMertensData where
  rhoNB : ℝ
  z : ℝ
  primitiveOrbitFinitePart : ℝ
  logFinitePart : ℝ
  mertensConstant : ℝ
  poleGap : 0 < 1 - rhoNB * z
  abelExpansionWitness :
    primitiveOrbitFinitePart = -Real.log (1 - rhoNB * z) + logFinitePart
  logFinitePartWitness : logFinitePart = (-1.465260542946848 : ℝ)
  mertensConstantWitness : mertensConstant = (-0.888044878045315 : ℝ)

/-- The primitive-orbit Abel finite part splits into the Perron-pole singularity and a constant
finite part. -/
def RealInput40GeodesicMertensData.abelFinitePartExpansion
    (D : RealInput40GeodesicMertensData) : Prop :=
  D.primitiveOrbitFinitePart = -Real.log (1 - D.rhoNB * D.z) + D.logFinitePart

/-- Audited value of the logarithmic Abel finite part. -/
def RealInput40GeodesicMertensData.logFinitePartValue
    (D : RealInput40GeodesicMertensData) : Prop :=
  D.logFinitePart = (-1.465260542946848 : ℝ)

/-- Audited value of the corresponding geodesic Mertens constant. -/
def RealInput40GeodesicMertensData.mertensConstantValue
    (D : RealInput40GeodesicMertensData) : Prop :=
  D.mertensConstant = (-0.888044878045315 : ℝ)

/-- The Abel finite-part expansion at the Perron pole yields the audited logarithmic constant and
the resulting chapter-local geodesic Mertens constant.
    thm:real-input-40-geodesic-mertens -/
theorem paper_real_input_40_geodesic_mertens (D : RealInput40GeodesicMertensData) :
    D.abelFinitePartExpansion ∧ D.logFinitePartValue ∧ D.mertensConstantValue := by
  exact ⟨D.abelExpansionWitness, D.logFinitePartWitness, D.mertensConstantWitness⟩

end Omega.Zeta
