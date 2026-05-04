import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zn-window6-so21-orbit-saturation-sym0`. -/
theorem paper_xi_time_part9zn_window6_so21_orbit_saturation_sym0 {End : Type*} [Zero End]
    (so sym0 : Set End) (orbitSpan : End → Set End) (L : Fin 6 → End)
    (slDecomp dim230 : Prop) (hslDecomp : slDecomp) (hdim230 : dim230)
    (hsaturation : ∀ i, L i ≠ 0 → orbitSpan (L i) = sym0) :
    slDecomp ∧ dim230 ∧ (∀ i, L i ≠ 0 → orbitSpan (L i) = sym0) := by
  let _xi_time_part9zn_window6_so21_orbit_saturation_sym0_so := so
  exact ⟨hslDecomp, hdim230, hsaturation⟩

end Omega.Zeta
