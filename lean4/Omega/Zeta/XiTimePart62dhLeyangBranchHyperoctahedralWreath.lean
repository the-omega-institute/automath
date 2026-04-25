import Omega.Zeta.XiTimePart62dLeyangBranchGraphAutomorphismWreath

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dh-leyang-branch-hyperoctahedral-wreath`. -/
theorem paper_xi_time_part62dh_leyang_branch_hyperoctahedral_wreath (n : ℕ) :
    Nonempty
      (xiLeyangBranchGraphAutomorphismModel n ≃
        ((Fin 5 → ((Fin (2 * n) → Fin 2) × Equiv.Perm (Fin (2 * n)))) ×
          Equiv.Perm (Fin 5))) := by
  rcases paper_xi_time_part62d_leyang_branch_graph_automorphism_wreath n with ⟨_, hEquiv, _, _⟩
  exact hEquiv

end Omega.Zeta
