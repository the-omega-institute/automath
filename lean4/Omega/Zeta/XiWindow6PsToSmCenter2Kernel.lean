import Mathlib.Tactic

namespace Omega.Zeta

/-- The canonical window-6 center, encoded as the eight-point Boolean cube. -/
def xi_window6_ps_to_sm_center2_kernel_canonical_center : Finset (Fin 3 → Bool) :=
  Finset.univ

/-- Concrete finite package for the center-compression argument. -/
structure xi_window6_ps_to_sm_center2_kernel_data where
  smTarget : Finset (Fin 3 → Bool)
  smTarget_card_le_four : smTarget.card ≤ 4
  centerToSM : (Fin 3 → Bool) → (Fin 3 → Bool)
  centerToSM_mem : ∀ x, centerToSM x ∈ smTarget

/-- The finite kernel claim: two distinct canonical-center elements have the same SM image. -/
def xi_window6_ps_to_sm_center2_kernel_data.claim
    (D : xi_window6_ps_to_sm_center2_kernel_data) : Prop :=
  ∃ x ∈ xi_window6_ps_to_sm_center2_kernel_canonical_center,
    ∃ y ∈ xi_window6_ps_to_sm_center2_kernel_canonical_center,
      x ≠ y ∧ D.centerToSM x = D.centerToSM y

/-- Paper label: `thm:xi-window6-ps-to-sm-center2-kernel`. -/
theorem paper_xi_window6_ps_to_sm_center2_kernel
    (D : xi_window6_ps_to_sm_center2_kernel_data) : D.claim := by
  classical
  by_contra hcollision
  have hInjective : Function.Injective D.centerToSM := by
    intro x y hxy
    by_contra hne
    exact hcollision
      ⟨x, by simp [xi_window6_ps_to_sm_center2_kernel_canonical_center],
        y, by simp [xi_window6_ps_to_sm_center2_kernel_canonical_center], hne, hxy⟩
  let compressed :
      (Fin 3 → Bool) → {b : Fin 3 → Bool // b ∈ D.smTarget} :=
    fun x => ⟨D.centerToSM x, D.centerToSM_mem x⟩
  have hCompressedInjective : Function.Injective compressed := by
    intro x y hxy
    apply hInjective
    exact congrArg Subtype.val hxy
  have hCardLe :
      Fintype.card (Fin 3 → Bool) ≤ Fintype.card {b : Fin 3 → Bool // b ∈ D.smTarget} :=
    Fintype.card_le_of_injective compressed hCompressedInjective
  have hTargetCard :
      Fintype.card {b : Fin 3 → Bool // b ∈ D.smTarget} = D.smTarget.card := by
    simp
  have hCubeCard : Fintype.card (Fin 3 → Bool) = 8 := by
    native_decide
  have hCompressedCardLeFour :
      Fintype.card {b : Fin 3 → Bool // b ∈ D.smTarget} ≤ 4 := by
    rw [hTargetCard]
    exact D.smTarget_card_le_four
  rw [hCubeCard] at hCardLe
  omega

end Omega.Zeta
