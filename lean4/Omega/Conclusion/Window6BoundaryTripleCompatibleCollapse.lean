import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the window-`6` boundary triple-compatible collapse. The three sets are the
three compatibility predicates; the collapse fact says their intersection is rationally invisible
for the recorded certificate degree. -/
structure conclusion_window6_boundary_triple_compatible_collapse_data where
  conclusion_window6_boundary_triple_compatible_collapse_space : Type
  conclusion_window6_boundary_triple_compatible_collapse_zero :
    conclusion_window6_boundary_triple_compatible_collapse_space
  conclusion_window6_boundary_triple_compatible_collapse_c3Equivariant :
    Set conclusion_window6_boundary_triple_compatible_collapse_space
  conclusion_window6_boundary_triple_compatible_collapse_geometricallyRealizable :
    Set conclusion_window6_boundary_triple_compatible_collapse_space
  conclusion_window6_boundary_triple_compatible_collapse_boundaryCompatible :
    Set conclusion_window6_boundary_triple_compatible_collapse_space
  conclusion_window6_boundary_triple_compatible_collapse_rationalCertificateDegree :
    conclusion_window6_boundary_triple_compatible_collapse_space → ℕ
  conclusion_window6_boundary_triple_compatible_collapse_invisible_of_compatible :
    ∀ v,
      v ∈ conclusion_window6_boundary_triple_compatible_collapse_c3Equivariant →
      v ∈ conclusion_window6_boundary_triple_compatible_collapse_geometricallyRealizable →
      v ∈ conclusion_window6_boundary_triple_compatible_collapse_boundaryCompatible →
        conclusion_window6_boundary_triple_compatible_collapse_rationalCertificateDegree v = 0

namespace conclusion_window6_boundary_triple_compatible_collapse_data

def statement
    (D : conclusion_window6_boundary_triple_compatible_collapse_data) : Prop :=
  ¬ ∃ v : D.conclusion_window6_boundary_triple_compatible_collapse_space,
    v ≠ D.conclusion_window6_boundary_triple_compatible_collapse_zero ∧
      v ∈ D.conclusion_window6_boundary_triple_compatible_collapse_c3Equivariant ∧
      v ∈ D.conclusion_window6_boundary_triple_compatible_collapse_geometricallyRealizable ∧
      v ∈ D.conclusion_window6_boundary_triple_compatible_collapse_boundaryCompatible ∧
      0 < D.conclusion_window6_boundary_triple_compatible_collapse_rationalCertificateDegree v

end conclusion_window6_boundary_triple_compatible_collapse_data

/-- Paper label: `thm:conclusion-window6-boundary-triple-compatible-collapse`. -/
theorem paper_conclusion_window6_boundary_triple_compatible_collapse
    (D : conclusion_window6_boundary_triple_compatible_collapse_data) : D.statement := by
  rintro ⟨v, _hv_nonzero, hv_c3, hv_geo, hv_boundary, hv_positive⟩
  have hv_zero :=
    D.conclusion_window6_boundary_triple_compatible_collapse_invisible_of_compatible
      v hv_c3 hv_geo hv_boundary
  omega

end Omega.Conclusion
