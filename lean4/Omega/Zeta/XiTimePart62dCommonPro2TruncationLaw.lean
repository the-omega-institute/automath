import Omega.Zeta.XiTimePart62dHologramImageCantorHomeomorphism
import Omega.Zeta.XiTerminalZmLeyangFiniteBranchRegular4aryAddress

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62d-common-pro2-truncation-law`. -/
theorem paper_xi_time_part62d_common_pro2_truncation_law
    (H : xi_time_part62d_hologram_image_cantor_homeomorphism_Data)
    (B : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :
    Function.Injective (xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap H) ∧
      (∀ i n,
        Nonempty
          (B.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i
              (n + 1) ≃
            B.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n ×
              Fin 4)) ∧
      Nonempty
        (xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitUnion B ≃
          Fin 5 × (ℕ → Fin 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap
    exact fun _ _ h => h
  · intro i n
    exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_oneStepEquiv B i n⟩
  · exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitEquiv B⟩

end Omega.Zeta
