import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-joukowsky-reciprocity-residue-duality`. -/
theorem paper_conclusion_joukowsky_reciprocity_residue_duality {A : Type} [Fintype A]
    [DecidableEq A] (ι : A → A) (outer inner residue : A → ℂ)
    (hinv : ∀ a, ι (ι a) = a) (hres : ∀ a, residue (ι a) = -residue a)
    (hweight : ∀ a, inner (ι a) = outer a) :
    (∑ a : A, outer a * residue a) = -∑ b : A, inner b * residue b := by
  classical
  let e : A ≃ A :=
    { toFun := ι
      invFun := ι
      left_inv := hinv
      right_inv := hinv }
  have hperm :
      (∑ a : A, inner (ι a) * residue (ι a)) = ∑ b : A, inner b * residue b := by
    exact Fintype.sum_equiv e (fun a => inner (ι a) * residue (ι a))
      (fun b => inner b * residue b) (fun _ => rfl)
  have hflip :
      (∑ a : A, inner (ι a) * residue (ι a)) =
        ∑ a : A, -(outer a * residue a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [hweight a, hres a]
  calc
    (∑ a : A, outer a * residue a) = -∑ a : A, -(outer a * residue a) := by
      simp
    _ = -∑ a : A, inner (ι a) * residue (ι a) := by
      rw [hflip]
    _ = -∑ b : A, inner b * residue b := by
      rw [hperm]

end Omega.Conclusion
