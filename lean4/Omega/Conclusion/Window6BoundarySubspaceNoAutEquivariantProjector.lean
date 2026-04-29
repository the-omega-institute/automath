import Mathlib.Tactic

namespace Omega.Conclusion

namespace Function

/-- Minimal local predicate for idempotent endomorphisms. -/
def Idempotent {α : Type*} (f : α → α) : Prop :=
  ∀ x, f (f x) = f x

end Function

/-- Concrete package for the window-`6` boundary-subspace obstruction. The automorphism action is
given by endomorphisms `act g`, and the distinguished boundary subspace is recorded by the set
`boundary`. The witness `boundaryPoint` lies in the boundary, but some automorphism sends it
outside. -/
structure conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data where
  V : Type
  aut : Type
  act : aut → V → V
  boundary : Set V
  boundaryPoint : V
  boundaryPoint_mem : boundaryPoint ∈ boundary
  boundaryPoint_breaks :
      ∃ g : aut, act g boundaryPoint ∉ boundary

namespace conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data

/-- Equivariance of an endomorphism with respect to the recorded automorphism action. -/
def aut_equivariant
    (D : conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data)
    (proj : D.V → D.V) : Prop :=
  ∀ g x, proj (D.act g x) = D.act g (proj x)

/-- The endomorphism has the boundary subspace as its image. -/
def has_boundary_image
    (D : conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data)
    (proj : D.V → D.V) : Prop :=
  Set.range proj = D.boundary

/-- The boundary subspace is invariant under the recorded automorphism action. -/
def boundary_invariant
    (D : conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data) : Prop :=
  ∀ g x, x ∈ D.boundary → D.act g x ∈ D.boundary

end conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data

open conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data

private lemma conclusion_window6_boundary_subspace_no_aut_equivariant_projector_image_invariant
    (D : conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data)
    {proj : D.V → D.V} (_hIdem : Function.Idempotent proj)
    (hEqv : D.aut_equivariant proj) (hImg : D.has_boundary_image proj) :
    D.boundary_invariant := by
  intro g x hx
  rw [← hImg] at hx
  rcases hx with ⟨y, rfl⟩
  rw [← hImg]
  refine ⟨D.act g y, ?_⟩
  exact hEqv g y

/-- Paper label:
`thm:conclusion-window6-boundary-subspace-no-aut-equivariant-projector`. The image of an
equivariant idempotent is automorphism-invariant, so it cannot equal the distinguished boundary
subspace once the boundary witness is moved outside by an automorphism. -/
theorem paper_conclusion_window6_boundary_subspace_no_aut_equivariant_projector
    (D : conclusion_window6_boundary_subspace_no_aut_equivariant_projector_data) :
    ¬ ∃ proj : D.V → D.V,
        Function.Idempotent proj ∧ D.aut_equivariant proj ∧ D.has_boundary_image proj := by
  rintro ⟨proj, hIdem, hEqv, hImg⟩
  have hInvariant :
      D.boundary_invariant :=
    conclusion_window6_boundary_subspace_no_aut_equivariant_projector_image_invariant
      D hIdem hEqv hImg
  rcases D.boundaryPoint_breaks with ⟨g, hg⟩
  exact hg (hInvariant g D.boundaryPoint D.boundaryPoint_mem)

end Omega.Conclusion
