import Omega.Zeta.XiTerminalZmLeyangFiniteBranchRegular4aryAddress

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dh-leyang-branch-affine-tate-regular-cover`. -/
theorem paper_xi_time_part62dh_leyang_branch_affine_tate_regular_cover
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :
    (∀ i n,
        Nonempty
          (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i (n + 1) ≃
            D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n ×
              Fin 4)) ∧
      Nonempty
        (xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitUnion D ≃
          Fin 5 × (ℕ → Fin 4)) := by
  refine ⟨?_, ?_⟩
  · intro i n
    exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_oneStepEquiv D i n⟩
  · exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitEquiv D⟩

end Omega.Zeta
