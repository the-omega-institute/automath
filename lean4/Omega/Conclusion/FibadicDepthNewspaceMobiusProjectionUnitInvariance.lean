import Mathlib.Data.Complex.Basic

namespace Omega.Conclusion

/-- Koopman transport by a finite unit action on the character ledger. -/
def conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_koopman
    {χ : Type*} (unitAction : Equiv.Perm χ) (f : χ → ℂ) : χ → ℂ :=
  fun x => f (unitAction.symm x)

/-- The exact-depth character span, represented by functions supported on one depth layer. -/
def conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_exactDepthSpan
    {χ : Type*} (depth : χ → ℕ) (d : ℕ) (f : χ → ℂ) : Prop :=
  ∀ x, depth x ≠ d → f x = 0

/-- The diagonal mask for the orthogonal projection onto one exact-depth layer. -/
def conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_projection
    {χ : Type*} (depth : χ → ℕ) (d : ℕ) (f : χ → ℂ) : χ → ℂ :=
  fun x => if depth x = d then f x else 0

/-- Paper-facing concrete statement for
`cor:conclusion-fibadic-depth-newspace-mobius-projection-unit-invariance`.

A depth-preserving unit permutation carries every exact-depth span to itself and
commutes with the diagonal Möbius/newspace projection onto that span. -/
def conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_statement : Prop :=
  ∀ {χ : Type*} (depth : χ → ℕ) (unitAction : Equiv.Perm χ)
    (_hdepth : ∀ x, depth (unitAction x) = depth x) (d : ℕ) (f : χ → ℂ),
      (conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_exactDepthSpan
          depth d f →
        conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_exactDepthSpan
          depth d
          (conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_koopman
            unitAction f)) ∧
      conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_koopman
          unitAction
          (conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_projection
            depth d f) =
        conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_projection
          depth d
          (conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_koopman
            unitAction f)

/-- Paper label:
`cor:conclusion-fibadic-depth-newspace-mobius-projection-unit-invariance`. -/
theorem paper_conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance :
    conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_statement := by
  intro χ depth unitAction hdepth d f
  constructor
  · intro hf x hx
    unfold conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_exactDepthSpan
      at hf
    unfold conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_koopman
    have hsymm : depth (unitAction.symm x) = depth x := by
      simpa using (hdepth (unitAction.symm x)).symm
    exact hf (unitAction.symm x) (by simpa [hsymm] using hx)
  · funext x
    unfold conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_koopman
      conclusion_fibadic_depth_newspace_mobius_projection_unit_invariance_projection
    have hsymm : depth (unitAction.symm x) = depth x := by
      simpa using (hdepth (unitAction.symm x)).symm
    by_cases hx : depth x = d <;> simp [hsymm, hx]

end Omega.Conclusion
