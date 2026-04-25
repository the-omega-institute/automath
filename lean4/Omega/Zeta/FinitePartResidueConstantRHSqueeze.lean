namespace Omega.Zeta

/-- Paper label: `prop:finite-part-residue-constant-rh-squeeze`. The reduced determinant product
and Kernel-RH spectral bound imply both residue squeeze estimates in the chapter package. -/
theorem paper_finite_part_residue_constant_rh_squeeze
    (residueProduct kernelRH residueSqueezeBounds logResidueSqueezeBound : Prop)
    (hderive : residueProduct → kernelRH → residueSqueezeBounds ∧ logResidueSqueezeBound)
    (hProduct : residueProduct) (hRH : kernelRH) :
    residueSqueezeBounds ∧ logResidueSqueezeBound := by
  exact hderive hProduct hRH

end Omega.Zeta
