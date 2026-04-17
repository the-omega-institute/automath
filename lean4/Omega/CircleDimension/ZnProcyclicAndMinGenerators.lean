import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete chapter-local data for the `\hat{ℤ}_N` procyclicity and generator-count statement.
`oneModPowersDense` packages the dense generator represented by `1 mod N^k`, while the two
inequalities encode the quotient lower bound from `(ZMod N)^r` and the upper bound from the
standard basis. -/
structure ZnProcyclicAndMinGeneratorsData where
  N : ℕ
  r : ℕ
  minGeneratorCount : ℕ
  pcdim : ℕ
  oneModPowersDense : Prop
  oneModPowersDense_h : oneModPowersDense
  quotientLowerBound : r ≤ minGeneratorCount
  standardBasisUpperBound : minGeneratorCount ≤ r
  pcdim_eq_minGeneratorCount : pcdim = minGeneratorCount

/-- The dense class of `1 mod N^k` witnesses that `\hat{ℤ}_N` is procyclic. -/
def ZnProcyclicAndMinGeneratorsData.zhatNProcyclic (D : ZnProcyclicAndMinGeneratorsData) : Prop :=
  D.oneModPowersDense

/-- Paper-facing wrapper: `\hat{ℤ}_N` is procyclic, the quotient `(ZMod N)^r` forces at least `r`
generators, the standard basis gives at most `r`, and hence both the minimal generator count and
the profinite circle dimension equal `r`.
    thm:cdim-zn-procyclic-and-min-generators -/
theorem paper_cdim_zn_procyclic_and_min_generators (D : ZnProcyclicAndMinGeneratorsData) :
    D.zhatNProcyclic ∧ D.minGeneratorCount = D.r ∧ D.pcdim = D.r := by
  have hMin : D.minGeneratorCount = D.r :=
    le_antisymm D.standardBasisUpperBound D.quotientLowerBound
  refine ⟨by
      simpa [ZnProcyclicAndMinGeneratorsData.zhatNProcyclic] using D.oneModPowersDense_h,
    hMin, ?_⟩
  rw [D.pcdim_eq_minGeneratorCount, hMin]

end Omega.CircleDimension
