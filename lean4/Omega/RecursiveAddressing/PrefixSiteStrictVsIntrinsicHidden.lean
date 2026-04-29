import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- Paper label: `prop:prefix-site-strict-vs-intrinsic-hidden`. -/
theorem paper_prefix_site_strict_vs_intrinsic_hidden {C2 H2 A : Type*} [AddCommGroup C2]
    [AddCommGroup H2] [AddCommGroup A] (incl : H2 →+ C2) (alphaTilde : C2 →+ A)
    (alphaBar : H2 →+ A) (hfactor : alphaBar = alphaTilde.comp incl) :
    alphaBar.range <= alphaTilde.range := by
  rw [hfactor]
  rintro _ ⟨h, rfl⟩
  exact ⟨incl h, rfl⟩

end Omega.RecursiveAddressing
