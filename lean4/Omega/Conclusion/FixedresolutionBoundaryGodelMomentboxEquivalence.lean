import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fixedresolution-boundary-godel-momentbox-equivalence`. -/
theorem paper_conclusion_fixedresolution_boundary_godel_momentbox_equivalence {U Phi Mom : Type*}
    (phi : U → Phi) (mom : U → Mom)
    (hphi : ∀ {u v : U}, phi u = phi v ↔ u = v)
    (hmom : ∀ {u v : U}, mom u = mom v ↔ u = v) (u v : U) :
    phi u = phi v ↔ mom u = mom v := by
  constructor
  · intro h
    exact hmom.mpr (hphi.mp h)
  · intro h
    exact hphi.mpr (hmom.mp h)

end Omega.Conclusion
