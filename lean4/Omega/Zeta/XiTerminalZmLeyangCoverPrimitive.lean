import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangMonodromyS4

namespace Omega.Zeta

/-- Data marker for the Lee--Yang quartic cover; the monodromy computation is supplied by
`paper_xi_terminal_zm_leyang_monodromy_s4`. -/
structure xi_terminal_zm_leyang_cover_primitive_data where
  xi_terminal_zm_leyang_cover_primitive_monodromy :
    xiLeyangGeometricMonodromyGroup = ⊤ := paper_xi_terminal_zm_leyang_monodromy_s4.1

namespace xi_terminal_zm_leyang_cover_primitive_data

def has_degree_two_factorization (_D : xi_terminal_zm_leyang_cover_primitive_data) : Prop :=
  ∃ B : Finset (Fin 4), B.card = 2 ∧
    ∀ σ : Equiv.Perm (Fin 4), B.image σ = B ∨ Disjoint (B.image σ) B

end xi_terminal_zm_leyang_cover_primitive_data

lemma xi_terminal_zm_leyang_cover_primitive_not_block_system :
    ¬ ∃ B : Finset (Fin 4), B.card = 2 ∧
      ∀ σ : Equiv.Perm (Fin 4), B.image σ = B ∨ Disjoint (B.image σ) B := by
  decide

/-- Paper label: `cor:xi-terminal-zm-leyang-cover-primitive`. -/
theorem paper_xi_terminal_zm_leyang_cover_primitive
    (D : xi_terminal_zm_leyang_cover_primitive_data) :
    ¬ D.has_degree_two_factorization := by
  simpa [xi_terminal_zm_leyang_cover_primitive_data.has_degree_two_factorization] using
    xi_terminal_zm_leyang_cover_primitive_not_block_system

end Omega.Zeta
