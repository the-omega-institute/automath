namespace Omega.Zeta

/-- Paper-facing wrapper for the cyclic-lift primitive-orbit package: the off-multiple vanishing
and the multiple closed form are recorded together.
    cor:zeta-cyclic-lift-primitive-orbits -/
theorem paper_zeta_cyclic_lift_primitive_orbits
    (q : Nat) (offMultiplesVanish multiplesHaveClosedForm : Prop)
    (zeta_cyclic_lift_primitive_orbits_off_multiples_vanish : offMultiplesVanish)
    (zeta_cyclic_lift_primitive_orbits_multiples_have_closed_form : multiplesHaveClosedForm) :
    offMultiplesVanish ∧ multiplesHaveClosedForm := by
  let _ := q
  exact ⟨zeta_cyclic_lift_primitive_orbits_off_multiples_vanish,
    zeta_cyclic_lift_primitive_orbits_multiples_have_closed_form⟩

end Omega.Zeta
