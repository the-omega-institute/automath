import Mathlib.Tactic

namespace Omega.Conclusion

/-- Abstract decode form of the squareclass boundary syndrome theorem: the supplied equivalence
identifies code membership with closedness, while `decode` constructs the unique bulk filling.
Paper label: `thm:conclusion-dyadic-boundary-squareclass-syndrome-unique-fill`. -/
theorem paper_conclusion_dyadic_boundary_squareclass_syndrome_unique_fill
    {Boundary Bulk : Type*} (inCode closed : Boundary → Prop) (fill : Bulk → Boundary)
    (decode : ∀ b, closed b → Bulk) (hiff : ∀ b, inCode b ↔ closed b)
    (hdecode : ∀ b h, fill (decode b h) = b)
    (hunique : ∀ b x y, fill x = b → fill y = b → x = y) (N : Boundary) :
    (inCode N ↔ closed N) ∧ (closed N → ∃! x : Bulk, fill x = N) := by
  refine ⟨hiff N, ?_⟩
  intro hclosed
  refine ⟨decode N hclosed, hdecode N hclosed, ?_⟩
  intro y hy
  exact hunique N y (decode N hclosed) hy (hdecode N hclosed)

end Omega.Conclusion
