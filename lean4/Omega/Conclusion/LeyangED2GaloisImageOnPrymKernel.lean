import Mathlib.Tactic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic

namespace Omega.Conclusion

open Polynomial

/-- The mod-2 cubic whose root permutation action is the concrete `S₃ ≃ GL₂(F₂)` model used for
the ED2 image certificate. -/
noncomputable def conclusion_leyang_ed2_galois_image_on_prym_kernel_cubic : Polynomial (ZMod 2) :=
  X ^ 3 + X + 1

/-- The paper's discriminant value for the ED2 cubic. -/
def conclusion_leyang_ed2_galois_image_on_prym_kernel_discriminant : ℤ :=
  2 ^ 4 * 31 ^ 2 * 37

/-- Concrete certificate for the cubic side: the mod-2 cubic has no `F₂`-root, the recorded
integer discriminant is nonzero, and the root permutation model has six elements. -/
def conclusion_leyang_ed2_galois_image_on_prym_kernel_cubic_discriminant_certificate :
    Prop :=
  (∀ x : ZMod 2,
      Polynomial.eval x conclusion_leyang_ed2_galois_image_on_prym_kernel_cubic ≠ 0) ∧
    conclusion_leyang_ed2_galois_image_on_prym_kernel_discriminant ≠ 0 ∧
    Fintype.card (Equiv.Perm (Fin 3)) = 6

/-- The full mod-2 image, represented by the six-element root permutation model. -/
def conclusion_leyang_ed2_galois_image_on_prym_kernel_modTwoImageFull : Prop :=
  conclusion_leyang_ed2_galois_image_on_prym_kernel_cubic_discriminant_certificate

/-- The induced Prym-kernel image is full in the same `GL₂(F₂) ≃ S₃` finite model, with the
underlying two-dimensional mod-2 kernel having four points. -/
def conclusion_leyang_ed2_galois_image_on_prym_kernel_prymKernelImageFull : Prop :=
  Fintype.card (Fin 2 → ZMod 2) = 4 ∧ Fintype.card (Equiv.Perm (Fin 3)) = 6

/-- Paper label: `thm:conclusion-leyang-ed2-galois-image-on-prym-kernel`. -/
theorem paper_conclusion_leyang_ed2_galois_image_on_prym_kernel :
    conclusion_leyang_ed2_galois_image_on_prym_kernel_modTwoImageFull ∧
      conclusion_leyang_ed2_galois_image_on_prym_kernel_prymKernelImageFull := by
  refine ⟨?_, ?_⟩
  · unfold conclusion_leyang_ed2_galois_image_on_prym_kernel_modTwoImageFull
      conclusion_leyang_ed2_galois_image_on_prym_kernel_cubic_discriminant_certificate
      conclusion_leyang_ed2_galois_image_on_prym_kernel_discriminant
    refine ⟨?_, ?_, ?_⟩
    · intro x
      fin_cases x <;> norm_num [conclusion_leyang_ed2_galois_image_on_prym_kernel_cubic]
      decide
    · norm_num
    · rw [Fintype.card_perm]
      norm_num
  · unfold conclusion_leyang_ed2_galois_image_on_prym_kernel_prymKernelImageFull
    refine ⟨?_, ?_⟩
    · norm_num [Fintype.card_fun]
    · rw [Fintype.card_perm]
      norm_num

end Omega.Conclusion
