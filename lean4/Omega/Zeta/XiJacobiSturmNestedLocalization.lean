namespace Omega.Zeta

/-- Paper label: `prop:xi-jacobi-sturm-nested-localization`.  Sturm interlacing gives the
nested squeeze package, and the nested squeeze package gives exact closure at the terminal
truncation. -/
theorem paper_xi_jacobi_sturm_nested_localization
    (sturmInterlacing nestedSqueeze exactClosure : Prop) (hInterlace : sturmInterlacing)
    (hNested : sturmInterlacing → nestedSqueeze) (hExact : nestedSqueeze → exactClosure) :
    sturmInterlacing ∧ nestedSqueeze ∧ exactClosure := by
  exact ⟨hInterlace, hNested hInterlace, hExact (hNested hInterlace)⟩

end Omega.Zeta
