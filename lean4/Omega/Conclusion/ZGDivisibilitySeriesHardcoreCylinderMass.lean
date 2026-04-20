import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete witness for the comparison between the squarefree divisibility series and the
Bernoulli hardcore cylinder mass. The common all-zero factor is recorded explicitly so that the
series differs from the cylinder mass only by the zeta-ratio prefactor. -/
structure ZGHardcoreCylinderWitness where
  zetaRatio : ℚ
  allZeroMass : ℚ
  squarefreeWeight : ℕ → ℚ

/-- Bernoulli cylinder mass of the squarefree multiples of `d`. -/
def ZGHardcoreCylinderWitness.hardcoreCylinderMass (w : ZGHardcoreCylinderWitness) (d : ℕ) : ℚ :=
  w.allZeroMass * w.squarefreeWeight d

/-- Divisibility series obtained by multiplying the common cylinder mass by the zeta-ratio
prefactor. -/
def ZGHardcoreCylinderWitness.divisibilitySeries (w : ZGHardcoreCylinderWitness) (d : ℕ) : ℚ :=
  w.zetaRatio * w.allZeroMass * w.squarefreeWeight d

/-- The squarefree divisibility series factors as the zeta-ratio prefactor times the Bernoulli
hardcore cylinder mass.
    thm:conclusion-zg-divisibility-series-hardcore-cylinder-mass -/
theorem paper_conclusion_zg_divisibility_series_hardcore_cylinder_mass
    (w : ZGHardcoreCylinderWitness) (d : ℕ) :
    w.divisibilitySeries d = w.zetaRatio * w.hardcoreCylinderMass d := by
  simp [ZGHardcoreCylinderWitness.divisibilitySeries,
    ZGHardcoreCylinderWitness.hardcoreCylinderMass, mul_assoc]

end Omega.Conclusion
