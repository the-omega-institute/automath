namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62d-solenoid-kronecker-rose-lissajous-lift`. -/
theorem paper_xi_time_part62d_solenoid_kronecker_rose_lissajous_lift
    (hom injective dense roseIdentity lissajousIdentity : Prop) (hHom : hom)
    (hInjective : injective) (hDense : dense) (hRose : hom -> roseIdentity)
    (hLissajous : hom -> lissajousIdentity) :
    hom ∧ injective ∧ dense ∧ roseIdentity ∧ lissajousIdentity := by
  exact ⟨hHom, hInjective, hDense, hRose hHom, hLissajous hHom⟩

end Omega.Zeta
