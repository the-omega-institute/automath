import Omega.Zeta.FinitePartDirichletCharacterInversionPrime

namespace Omega.Zeta

/-- Paper label: `cor:finite-part-dirichlet-character-projection`. -/
theorem paper_finite_part_dirichlet_character_projection {q : Nat}
    (V : PrimeUnitClass q → Complex) (χ : PrimeUnitClass q) : gaussDirichletCoeff q V χ = V χ := by
  simp [gaussDirichletCoeff]

end Omega.Zeta
