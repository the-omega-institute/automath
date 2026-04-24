import Mathlib.Tactic
import Omega.Zeta.XiTimePart65dChainInteriorIntervalSquarefreeDivisorIsomorphism

namespace Omega.Zeta

open Finset

/-- Paper-facing height formula for the arithmeticized chain-interior interval. The bottom element
is the singleton `{0}`, the top element is the full fixed-point set, and the arithmetic height is
the size of the transported squarefree support. -/
def xi_time_part9zl_chain_arithmetic_height_formula_statement (n : Nat) : Prop :=
  let I : Finset (Fin (n + 1)) := {0}
  let J : Finset (Fin (n + 1)) := Finset.univ
  ∃ e :
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J ≃
        xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_interval
          I J,
    (∀ K,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
          e K =
        Omega.Folding.chainInteriorGodelCode (K.1 \ I)) ∧
    ∀ K, K.1.card - 1 = (e K).1.card

/-- Paper label: `thm:xi-time-part9zl-chain-arithmetic-height-formula`. The existing interval /
squarefree-divisor equivalence identifies the chain-interior height above `{0}` with the number of
free squarefree support coordinates. -/
theorem paper_xi_time_part9zl_chain_arithmetic_height_formula (n : Nat) :
    xi_time_part9zl_chain_arithmetic_height_formula_statement n := by
  classical
  dsimp [xi_time_part9zl_chain_arithmetic_height_formula_statement]
  let I : Finset (Fin (n + 1)) := {0}
  let J : Finset (Fin (n + 1)) := Finset.univ
  have hIJ : I ⊆ J := by
    simp [I, J]
  refine
    ⟨xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_equiv hIJ, ?_, ?_⟩
  · intro K
    rfl
  · intro K
    change K.1.card - 1 = (K.1 \ I).card
    symm
    simpa [I] using (Finset.card_sdiff_of_subset K.2.1)

end Omega.Zeta
