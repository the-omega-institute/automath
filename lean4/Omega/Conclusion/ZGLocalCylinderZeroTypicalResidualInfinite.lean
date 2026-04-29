import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zg-local-cylinder-zero-typical-residual-infinite`. -/
theorem paper_conclusion_zg_local_cylinder_zero_typical_residual_infinite
    {Point Cylinder : Type*} (U : Cylinder → Point → Prop) (nonempty : Cylinder → Prop)
    (aeZeroOn denseGdeltaInfiniteOn : (Point → Prop) → Prop)
    (hzero : ∀ C, nonempty C → aeZeroOn (U C))
    (hinfty : ∀ C, nonempty C → denseGdeltaInfiniteOn (U C)) :
    ∀ C, nonempty C → aeZeroOn (U C) ∧ denseGdeltaInfiniteOn (U C) := by
  intro C hC
  exact ⟨hzero C hC, hinfty C hC⟩

end Omega.Conclusion
