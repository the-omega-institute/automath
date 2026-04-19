namespace Omega.CircleDimension

/-- Paper-facing package for the two-axis product laws.
    thm:gcdim-two-axis-product-laws -/
theorem paper_gcdim_two_axis_product_laws
    (linearDisjoint trdegAdditive degreeMultiplicative : Prop)
    (hLD : linearDisjoint)
    (hTrdeg : trdegAdditive)
    (hDeg : linearDisjoint → trdegAdditive → degreeMultiplicative) :
    trdegAdditive ∧ degreeMultiplicative := by
  exact ⟨hTrdeg, hDeg hLD hTrdeg⟩

end Omega.CircleDimension
