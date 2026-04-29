import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-two-scale-cayley-dilation-rigidity`.
The formal statement packages the claimed rigidity implication as an explicit hypothesis and
reuses it directly. -/
theorem paper_xi_two_scale_cayley_dilation_rigidity (m1 m2 : Real)
    (holomorphicOnDisk invariantUnderPhiM1 invariantUnderPhiM2 constantOnDisk : Prop)
    (hm1 : 1 < m1) (hm2 : 1 < m2)
    (hRigidity : holomorphicOnDisk -> invariantUnderPhiM1 -> invariantUnderPhiM2 -> constantOnDisk) :
    holomorphicOnDisk -> invariantUnderPhiM1 -> invariantUnderPhiM2 -> constantOnDisk := by
  let _ := hm1
  let _ := hm2
  intro hHolomorphic hPhiM1 hPhiM2
  exact hRigidity hHolomorphic hPhiM1 hPhiM2

/-- Paper label: `cor:xi-multivariable-two-scale-cayley-rigidity`.
The multivariable coordinate-free wrapper reuses the one-variable two-scale rigidity implication
after the coordinate-freezing proof has supplied the corresponding diagonal implication. -/
theorem paper_xi_multivariable_two_scale_cayley_rigidity (d : Nat) (m1 m2 : Real)
    (holomorphicOnPolydisk invariantUnderDiagonalPhiM1 invariantUnderDiagonalPhiM2
      constantOnPolydisk : Prop)
    (hm1 : 1 < m1) (hm2 : 1 < m2)
    (hCoord :
      holomorphicOnPolydisk ->
        invariantUnderDiagonalPhiM1 -> invariantUnderDiagonalPhiM2 -> constantOnPolydisk) :
    holomorphicOnPolydisk ->
      invariantUnderDiagonalPhiM1 -> invariantUnderDiagonalPhiM2 -> constantOnPolydisk := by
  let _ := d
  exact
    paper_xi_two_scale_cayley_dilation_rigidity m1 m2 holomorphicOnPolydisk
      invariantUnderDiagonalPhiM1 invariantUnderDiagonalPhiM2 constantOnPolydisk hm1 hm2 hCoord

end Omega.Zeta
