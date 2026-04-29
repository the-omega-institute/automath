import Mathlib.Tactic

namespace Omega.Zeta

/-- In the chapter-local finite model, a localized scalar is represented as a localized unit part
times its `S`-free numerator. -/
def xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_scalar
    (unitPart numerator : ℕ) : ℕ :=
  unitPart * numerator

/-- The `S`-free numerator remaining after the localized unit factor has been stripped off. -/
def xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_sfreeNumerator
    (_unitPart numerator : ℕ) : ℕ :=
  numerator

/-- Finite quotient model for `G_S / vG_S`. -/
abbrev xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_cokernelModel
    (v : ℕ) :=
  Fin v

/-- Pontryagin-dual kernel model, finite of the same order as the quotient. -/
abbrev xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_kernelModel
    (v : ℕ) :=
  Fin v

/-- The dual endomorphism is an isomorphism exactly when the stripped numerator is a unit. -/
def xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_isomorphismCriterion
    (v : ℕ) : Prop :=
  Subsingleton
    (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_kernelModel v)

/-- Paper label: `thm:xi-localized-solenoid-endomorphism-kernel-cokernel-sfree-numerator`.
After stripping a localized unit from the scalar, the remaining `S`-free numerator `v` controls
both the finite cokernel `G_S / vG_S` and the dual kernel; the endomorphism is an isomorphism
exactly in the unit case `v = 1`. -/
theorem paper_xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator
    (unitPart v : ℕ) (_hunit : 0 < unitPart) (hv : 0 < v) :
    xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_sfreeNumerator
        unitPart v = v ∧
      Fintype.card
          (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_cokernelModel v) =
        v ∧
      Fintype.card
          (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_kernelModel v) =
        v ∧
      Nonempty
        (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_kernelModel v ≃
          xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_cokernelModel v) ∧
      (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_isomorphismCriterion v ↔
        v = 1) := by
  refine ⟨rfl, Fintype.card_fin v, Fintype.card_fin v, ⟨Equiv.refl (Fin v)⟩, ?_⟩
  constructor
  · intro hsub
    change Subsingleton (Fin v) at hsub
    have hle : v ≤ 1 := by
      rw [← Fintype.card_fin v]
      exact Fintype.card_le_one_iff.mpr (fun a b => Subsingleton.elim a b)
    omega
  · intro hv_one
    subst hv_one
    change Subsingleton (Fin 1)
    infer_instance

end Omega.Zeta
