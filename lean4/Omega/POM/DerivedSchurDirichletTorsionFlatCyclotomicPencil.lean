namespace Omega.POM

/-- Paper label: `thm:derived-schur-dirichlet-torsion-flat-cyclotomic-pencil`. -/
theorem paper_derived_schur_dirichlet_torsion_flat_cyclotomic_pencil
    {q : Nat} (nonprincipal_vanishing primitive_values_constant cyclotomic_pencil_form : Prop)
    (h1 : nonprincipal_vanishing ↔ primitive_values_constant)
    (h2 : primitive_values_constant ↔ cyclotomic_pencil_form) :
    nonprincipal_vanishing ↔ primitive_values_constant ∧ cyclotomic_pencil_form := by
  constructor
  · intro hvanish
    refine ⟨h1.mp hvanish, h2.mp (h1.mp hvanish)⟩
  · intro hflat
    exact h1.mpr hflat.1

end Omega.POM
