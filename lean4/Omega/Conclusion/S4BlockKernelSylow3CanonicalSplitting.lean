import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-!
Concrete finite bookkeeping model for
`thm:conclusion-s4-block-kernel-sylow3-canonical-splitting`.

The block kernel is represented by one `ZMod 3` coordinate on each of the
forty four-point blocks.  Coordinate projections and coordinate kernels give
the canonical product decomposition.
-/

abbrev conclusion_s4_block_kernel_sylow3_canonical_splitting_Block : Type :=
  Fin 40

abbrev conclusion_s4_block_kernel_sylow3_canonical_splitting_Coordinate : Type :=
  ZMod 3

abbrev conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel : Type :=
  conclusion_s4_block_kernel_sylow3_canonical_splitting_Block →
    conclusion_s4_block_kernel_sylow3_canonical_splitting_Coordinate

abbrev conclusion_s4_block_kernel_sylow3_canonical_splitting_Data : Type :=
  Unit

def conclusion_s4_block_kernel_sylow3_canonical_splitting_projection
    (_D : conclusion_s4_block_kernel_sylow3_canonical_splitting_Data)
    (j : conclusion_s4_block_kernel_sylow3_canonical_splitting_Block)
    (x : conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel) :
    conclusion_s4_block_kernel_sylow3_canonical_splitting_Coordinate :=
  x j

def conclusion_s4_block_kernel_sylow3_canonical_splitting_coordinateKernel
    (D : conclusion_s4_block_kernel_sylow3_canonical_splitting_Data)
    (j : conclusion_s4_block_kernel_sylow3_canonical_splitting_Block) :
    Set conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel :=
  {x | conclusion_s4_block_kernel_sylow3_canonical_splitting_projection D j x = 0}

def conclusion_s4_block_kernel_sylow3_canonical_splitting_Data.sylow3_is_elementary_abelian
    (_D : conclusion_s4_block_kernel_sylow3_canonical_splitting_Data) : Prop :=
  Fintype.card conclusion_s4_block_kernel_sylow3_canonical_splitting_Coordinate = 3 ∧
    Fintype.card conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel = 3 ^ 40

def conclusion_s4_block_kernel_sylow3_canonical_splitting_Data.has_canonical_block_product
    (D : conclusion_s4_block_kernel_sylow3_canonical_splitting_Data) : Prop :=
  (∀ x : conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel,
      (fun j =>
          conclusion_s4_block_kernel_sylow3_canonical_splitting_projection D j x) = x) ∧
    ∀ (j : conclusion_s4_block_kernel_sylow3_canonical_splitting_Block)
      (x : conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel),
      x ∈ conclusion_s4_block_kernel_sylow3_canonical_splitting_coordinateKernel D j ↔
        conclusion_s4_block_kernel_sylow3_canonical_splitting_projection D j x = 0

/-- thm:conclusion-s4-block-kernel-sylow3-canonical-splitting -/
theorem paper_conclusion_s4_block_kernel_sylow3_canonical_splitting
    (D : conclusion_s4_block_kernel_sylow3_canonical_splitting_Data) :
    D.sylow3_is_elementary_abelian ∧ D.has_canonical_block_product := by
  constructor
  · constructor <;> simp [conclusion_s4_block_kernel_sylow3_canonical_splitting_Kernel,
      conclusion_s4_block_kernel_sylow3_canonical_splitting_Coordinate]
  · constructor
    · intro x
      rfl
    · intro j x
      rfl

end Omega.Conclusion
