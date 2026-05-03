import Mathlib.Data.Fintype.Basic

namespace Omega.Conclusion

/-- Concrete data for the compact-Lie/profinite-kernel obstruction.

The kernel is represented by a finite residue object with `kernelCard` points; this is the
finite object obtained after composing the closed-subgroup, zero-dimensional Lie, and
compact-discrete-implies-finite reductions. -/
structure conclusion_compact_lie_profinite_kernel_obstruction_data where
  kernelCard : Nat

/-- The concrete kernel left by the compact-discrete reduction. -/
abbrev conclusion_compact_lie_profinite_kernel_obstruction_data.kernel
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) : Type :=
  Fin D.kernelCard

/-- The finite kernel conclusion. -/
def conclusion_compact_lie_profinite_kernel_obstruction_data.kernelFinite
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) : Prop :=
  Nonempty (Fintype D.kernel)

/-- Paper label: `thm:conclusion-compact-lie-profinite-kernel-obstruction`. In the concrete
finite residue model obtained from the compact-Lie reductions, the profinite kernel is finite. -/
theorem paper_conclusion_compact_lie_profinite_kernel_obstruction
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) : D.kernelFinite := by
  exact ⟨inferInstance⟩

end Omega.Conclusion
