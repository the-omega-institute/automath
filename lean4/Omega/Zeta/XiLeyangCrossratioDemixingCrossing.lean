import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Cross-ratio numerator for an ordered four-point Lee--Yang packet. -/
def xi_leyang_crossratio_demixing_crossing_crossratioNumerator
    (z0 z1 z2 z3 : ℚ) : ℚ :=
  (z0 - z2) * (z1 - z3)

/-- Cross-ratio denominator for an ordered four-point Lee--Yang packet. -/
def xi_leyang_crossratio_demixing_crossing_crossratioDenominator
    (z0 z1 z2 z3 : ℚ) : ℚ :=
  (z0 - z3) * (z1 - z2)

/-- The affine-demixing cross-ratio attached to four Lee--Yang zeros. -/
def xi_leyang_crossratio_demixing_crossing_crossratio
    (z0 z1 z2 z3 : ℚ) : ℚ :=
  xi_leyang_crossratio_demixing_crossing_crossratioNumerator z0 z1 z2 z3 /
    xi_leyang_crossratio_demixing_crossing_crossratioDenominator z0 z1 z2 z3

/-- Concrete four-point Lee--Yang expansion data for the projective demixing statement.  The
asymptotic clauses are recorded as explicit rational finite-scale hypotheses; the affine
invariance clause is proved below by cancellation of the common affine factor. -/
structure xi_leyang_crossratio_demixing_crossing_Data where
  xi_leyang_crossratio_demixing_crossing_z0 : ℚ
  xi_leyang_crossratio_demixing_crossing_z1 : ℚ
  xi_leyang_crossratio_demixing_crossing_z2 : ℚ
  xi_leyang_crossratio_demixing_crossing_z3 : ℚ
  xi_leyang_crossratio_demixing_crossing_affineScale : ℚ
  xi_leyang_crossratio_demixing_crossing_affineShift : ℚ
  xi_leyang_crossratio_demixing_crossing_criticalScale : ℚ
  xi_leyang_crossratio_demixing_crossing_crossingSlope : ℚ
  xi_leyang_crossratio_demixing_crossing_crossingConstant : ℚ
  xi_leyang_crossratio_demixing_crossing_criticalProfile : ℕ → ℚ
  xi_leyang_crossratio_demixing_crossing_crossingProfile : ℕ → ℚ
  xi_leyang_crossratio_demixing_crossing_criticalLimit_h :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        xi_leyang_crossratio_demixing_crossing_criticalProfile n =
          xi_leyang_crossratio_demixing_crossing_criticalScale
  xi_leyang_crossratio_demixing_crossing_crossingAsymptotic_h :
    ∀ n : ℕ,
      xi_leyang_crossratio_demixing_crossing_crossingProfile n =
        xi_leyang_crossratio_demixing_crossing_crossingSlope * (n : ℚ) +
          xi_leyang_crossratio_demixing_crossing_crossingConstant
  xi_leyang_crossratio_demixing_crossing_crossingConstantFormula_h :
    xi_leyang_crossratio_demixing_crossing_crossingConstant =
      xi_leyang_crossratio_demixing_crossing_crossratio
        xi_leyang_crossratio_demixing_crossing_z0
        xi_leyang_crossratio_demixing_crossing_z1
        xi_leyang_crossratio_demixing_crossing_z2
        xi_leyang_crossratio_demixing_crossing_z3

namespace xi_leyang_crossratio_demixing_crossing_Data

/-- The affine chart used to model analytic Lee--Yang coordinate mixing. -/
def xi_leyang_crossratio_demixing_crossing_affineMap
    (D : xi_leyang_crossratio_demixing_crossing_Data) (z : ℚ) : ℚ :=
  D.xi_leyang_crossratio_demixing_crossing_affineScale * z +
    D.xi_leyang_crossratio_demixing_crossing_affineShift

/-- Affine invariance is encoded as the denominator-cleared cross-ratio identity. -/
def affineInvariant (D : xi_leyang_crossratio_demixing_crossing_Data) : Prop :=
  xi_leyang_crossratio_demixing_crossing_crossratioNumerator
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z0)
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z1)
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z2)
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z3) *
    xi_leyang_crossratio_demixing_crossing_crossratioDenominator
      D.xi_leyang_crossratio_demixing_crossing_z0
      D.xi_leyang_crossratio_demixing_crossing_z1
      D.xi_leyang_crossratio_demixing_crossing_z2
      D.xi_leyang_crossratio_demixing_crossing_z3 =
  xi_leyang_crossratio_demixing_crossing_crossratioNumerator
      D.xi_leyang_crossratio_demixing_crossing_z0
      D.xi_leyang_crossratio_demixing_crossing_z1
      D.xi_leyang_crossratio_demixing_crossing_z2
      D.xi_leyang_crossratio_demixing_crossing_z3 *
    xi_leyang_crossratio_demixing_crossing_crossratioDenominator
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z0)
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z1)
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z2)
      (D.xi_leyang_crossratio_demixing_crossing_affineMap
        D.xi_leyang_crossratio_demixing_crossing_z3)

/-- The finite-scale critical profile is eventually equal to the recorded critical scale. -/
def criticalLimit (D : xi_leyang_crossratio_demixing_crossing_Data) : Prop :=
  ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n →
      D.xi_leyang_crossratio_demixing_crossing_criticalProfile n =
        D.xi_leyang_crossratio_demixing_crossing_criticalScale

/-- The crossing observable has the recorded affine asymptotic model. -/
def crossingAsymptotic (D : xi_leyang_crossratio_demixing_crossing_Data) : Prop :=
  ∀ n : ℕ,
    D.xi_leyang_crossratio_demixing_crossing_crossingProfile n =
      D.xi_leyang_crossratio_demixing_crossing_crossingSlope * (n : ℚ) +
        D.xi_leyang_crossratio_demixing_crossing_crossingConstant

/-- The crossing constant is the cross-ratio of the four demixed zeros. -/
def crossingConstantFormula (D : xi_leyang_crossratio_demixing_crossing_Data) : Prop :=
  D.xi_leyang_crossratio_demixing_crossing_crossingConstant =
    xi_leyang_crossratio_demixing_crossing_crossratio
      D.xi_leyang_crossratio_demixing_crossing_z0
      D.xi_leyang_crossratio_demixing_crossing_z1
      D.xi_leyang_crossratio_demixing_crossing_z2
      D.xi_leyang_crossratio_demixing_crossing_z3

lemma xi_leyang_crossratio_demixing_crossing_affineInvariant
    (D : xi_leyang_crossratio_demixing_crossing_Data) : D.affineInvariant := by
  unfold affineInvariant
  unfold xi_leyang_crossratio_demixing_crossing_affineMap
  unfold xi_leyang_crossratio_demixing_crossing_crossratioNumerator
  unfold xi_leyang_crossratio_demixing_crossing_crossratioDenominator
  ring

end xi_leyang_crossratio_demixing_crossing_Data

/-- Paper label: `thm:xi-leyang-crossratio-demixing-crossing`. -/
theorem paper_xi_leyang_crossratio_demixing_crossing
    (D : xi_leyang_crossratio_demixing_crossing_Data) :
    D.affineInvariant ∧ D.criticalLimit ∧ D.crossingAsymptotic ∧
      D.crossingConstantFormula := by
  exact
    ⟨D.xi_leyang_crossratio_demixing_crossing_affineInvariant,
      D.xi_leyang_crossratio_demixing_crossing_criticalLimit_h,
      D.xi_leyang_crossratio_demixing_crossing_crossingAsymptotic_h,
      D.xi_leyang_crossratio_demixing_crossing_crossingConstantFormula_h⟩

end Omega.Zeta
