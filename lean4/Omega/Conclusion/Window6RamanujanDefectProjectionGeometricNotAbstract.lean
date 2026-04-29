import Mathlib.Tactic

namespace Omega.Conclusion

/-- Invariance under all abstract automorphisms of the recorded action. -/
def conclusion_window6_ramanujan_defect_projection_geometric_not_abstract_invariant
    {V G : Type} (act : G → V → V) (S : Set V) : Prop :=
  ∀ g x, x ∈ S → act g x ∈ S

/-- A boundary subspace moved by an automorphism cannot be recovered by an invariant abstract
construction, hence neither can a defect projection whose support is exactly that boundary. -/
def conclusion_window6_ramanujan_defect_projection_geometric_not_abstract_statement : Prop :=
  ∀ (V G : Type) (act : G → V → V) (boundary : Set V),
    (∃ x, x ∈ boundary ∧ ∃ g, act g x ∉ boundary) →
      ¬ ∃ support : Set V,
        conclusion_window6_ramanujan_defect_projection_geometric_not_abstract_invariant
            act support ∧
          support = boundary

/-- Paper label:
`prop:conclusion-window6-ramanujan-defect-projection-geometric-not-abstract`. -/
theorem paper_conclusion_window6_ramanujan_defect_projection_geometric_not_abstract :
    conclusion_window6_ramanujan_defect_projection_geometric_not_abstract_statement := by
  intro V G act boundary hmoved
  rintro ⟨support, hsupport, rfl⟩
  rcases hmoved with ⟨x, hx, g, hg⟩
  exact hg (hsupport g x hx)

end Omega.Conclusion
