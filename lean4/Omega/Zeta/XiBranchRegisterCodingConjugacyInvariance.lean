import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-branch-register-coding-conjugacy-invariance`. -/
theorem paper_xi_branch_register_coding_conjugacy_invariance {Hist Code Code' : Type*}
    (C : Hist ≃ Code) (C' : Hist ≃ Code') (σ : Hist → Hist) :
    ∃ Γ : Code ≃ Code',
      ∀ z : Code, Γ (C (σ (C.symm z))) = C' (σ (C'.symm (Γ z))) := by
  refine ⟨C.symm.trans C', ?_⟩
  intro z
  simp

end Omega.Zeta
