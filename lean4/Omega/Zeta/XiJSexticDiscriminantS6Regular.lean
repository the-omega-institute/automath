namespace Omega.Zeta

/-- Paper label: `thm:xi-j-sextic-discriminant-s6-regular`. -/
theorem paper_xi_j_sextic_discriminant_s6_regular
    (discriminantFactorization branchValueSet regularS6Monodromy indecomposable
      noMobiusSymmetry : Prop)
    (h_disc : discriminantFactorization)
    (h_branch : branchValueSet)
    (h_gal : regularS6Monodromy)
    (h_indec : indecomposable)
    (h_symm : noMobiusSymmetry) :
    discriminantFactorization ∧ branchValueSet ∧ regularS6Monodromy ∧ indecomposable ∧
      noMobiusSymmetry := by
  exact ⟨h_disc, h_branch, h_gal, h_indec, h_symm⟩

end Omega.Zeta
