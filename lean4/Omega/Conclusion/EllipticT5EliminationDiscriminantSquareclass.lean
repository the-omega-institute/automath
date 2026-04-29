import Omega.Conclusion.EllipticT5UniqueQuadraticSubfield
import Omega.Zeta.XiLeyangImageFiveTorsionEliminationIrreducibilityDiscriminant

namespace Omega.Conclusion

/-- Degree of the concrete five-division elimination polynomial certificate. -/
def conclusion_elliptic_t5_elimination_discriminant_squareclass_degree : ℕ :=
  Omega.Zeta.xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_degree

/-- Paper label: `thm:conclusion-elliptic-t5-elimination-discriminant-squareclass`. -/
theorem paper_conclusion_elliptic_t5_elimination_discriminant_squareclass :
    conclusion_elliptic_t5_elimination_discriminant_squareclass_degree = 24 ∧
      ellipticT5QuadraticSubfieldDiscriminant = 5 := by
  rcases Omega.Zeta.paper_xi_leyang_image_five_torsion_elimination_irreducibility_discriminant
    with ⟨hdegree, _hlead, _hprime, _hmod3, _hsquare, _hfactors, _hexponents, _hd5⟩
  constructor
  · simpa [conclusion_elliptic_t5_elimination_discriminant_squareclass_degree] using hdegree
  · simp [ellipticT5QuadraticSubfieldDiscriminant]

end Omega.Conclusion
