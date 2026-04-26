import Omega.Zeta.XiTerminalZmLeyangFiniteBranchRegular4aryAddress

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62a-leyang-branch-inverse-limit-five-z2x2`. -/
theorem paper_xi_time_part62a_leyang_branch_inverse_limit_five_z2x2
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :
    Nonempty
      (xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitUnion D ≃
        Fin 5 × (ℕ → Fin 2 × Fin 2)) := by
  let digitEquiv : Fin 4 ≃ Fin 2 × Fin 2 :=
    (finCongr (by norm_num : 4 = 2 * 2)).trans finProdFinEquiv.symm
  let streamEquiv : (ℕ → Fin 4) ≃ (ℕ → Fin 2 × Fin 2) :=
    Equiv.piCongrRight fun _ => digitEquiv
  exact ⟨(xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitEquiv D).trans
    (Equiv.prodCongr (Equiv.refl (Fin 5)) streamEquiv)⟩

end Omega.Zeta
