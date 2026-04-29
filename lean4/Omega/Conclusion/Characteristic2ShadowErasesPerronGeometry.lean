import Mathlib.Data.ZMod.Basic

namespace Omega.Conclusion

/-- The mod-two factorization shadow keeps all spectral points in the two-point set `{0, 1}`. -/
def conclusion_characteristic2_shadow_erases_perron_geometry_mod_two_factorization
    (spectrum : Set (ZMod 2)) : Prop :=
  spectrum ⊆ ({0, 1} : Set (ZMod 2))

/-- Perron and non-real spectral geometry are erased in the characteristic-two shadow. -/
def conclusion_characteristic2_shadow_erases_perron_geometry_perron_geometry_erased
    (spectrum : Set (ZMod 2)) : Prop :=
  ∀ z : ZMod 2, z ∈ spectrum → z = 0 ∨ z = 1

/-- Paper label: `prop:conclusion-characteristic2-shadow-erases-perron-geometry`. -/
theorem paper_conclusion_characteristic2_shadow_erases_perron_geometry
    (spectrum : Set (ZMod 2))
    (hModTwo :
      conclusion_characteristic2_shadow_erases_perron_geometry_mod_two_factorization spectrum) :
    conclusion_characteristic2_shadow_erases_perron_geometry_perron_geometry_erased spectrum := by
  intro z hz
  simpa [conclusion_characteristic2_shadow_erases_perron_geometry_mod_two_factorization]
    using hModTwo hz

end Omega.Conclusion
