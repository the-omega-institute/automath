namespace Omega.Zeta

/-- Paper label: `thm:xi-finite-symmetric-atomic-carath-rh-equivalence`. -/
theorem paper_xi_finite_symmetric_atomic_carath_rh_equivalence
    (RH finiteSymmetricAtomicCarathApprox : Prop)
    (h_forward : RH → finiteSymmetricAtomicCarathApprox)
    (h_backward : finiteSymmetricAtomicCarathApprox → RH) :
    RH ↔ finiteSymmetricAtomicCarathApprox := by
  exact ⟨h_forward, h_backward⟩

end Omega.Zeta
