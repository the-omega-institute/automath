import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmJgSignedPermutationRepresentation

namespace Omega.Zeta

/-- Concrete wrapper datum for the `W(D_n)` forcing corollary. -/
structure xi_terminal_zm_jg_wdn_forced_data where
  xi_terminal_zm_jg_wdn_forced_witness : Unit := ()

/-- The even-sign subgroup singled out by the parity law. -/
abbrev xi_terminal_zm_jg_wdn_forced_even_signed_subgroup :=
  {g : xi_terminal_zm_jg_signed_permutation_representation_model //
    xi_terminal_zm_jg_signed_permutation_representation_weyl_D_subgroup g}

/-- The permutation quotient remembers only the `S₅` component. -/
def xi_terminal_zm_jg_wdn_forced_permutation_quotient
    (g : xi_terminal_zm_jg_wdn_forced_even_signed_subgroup) : Equiv.Perm (Fin 5) :=
  g.1.2

/-- The all-positive sign vector lies in the even-sign kernel. -/
def xi_terminal_zm_jg_wdn_forced_trivial_sign_vector :
    xi_terminal_zm_jg_signed_permutation_representation_sign_vector :=
  fun _ => false

lemma xi_terminal_zm_jg_wdn_forced_trivial_sign_vector_even :
    xi_terminal_zm_jg_signed_permutation_representation_even_parity
      xi_terminal_zm_jg_wdn_forced_trivial_sign_vector := by
  simp [xi_terminal_zm_jg_signed_permutation_representation_even_parity,
    xi_terminal_zm_jg_signed_permutation_representation_local_sign_of_vector,
    xi_terminal_zm_jg_wdn_forced_trivial_sign_vector, xiTerminalLocalSignProduct]

lemma xi_terminal_zm_jg_wdn_forced_permutation_quotient_surjective :
    Function.Surjective xi_terminal_zm_jg_wdn_forced_permutation_quotient := by
  intro π
  refine ⟨⟨(xi_terminal_zm_jg_wdn_forced_trivial_sign_vector, π), ?_⟩, rfl⟩
  exact xi_terminal_zm_jg_wdn_forced_trivial_sign_vector_even

/-- Concrete paper-facing formulation of the `W(D_n)` forcing package. -/
def xi_terminal_zm_jg_wdn_forced_statement (_D : xi_terminal_zm_jg_wdn_forced_data) : Prop :=
  Function.Injective xi_terminal_zm_jg_signed_permutation_representation_toPerm ∧
    (∀ g : xi_terminal_zm_jg_signed_permutation_representation_model, ∀ totalFrobeniusSign : ℤˣ,
      totalFrobeniusSign =
          xiTerminalLocalSignProduct
            (xi_terminal_zm_jg_signed_permutation_representation_local_sign_of_vector g.1) →
      totalFrobeniusSign = xiTerminalQsqrtNegThreeCharacter 1 →
      xi_terminal_zm_jg_signed_permutation_representation_weyl_D_subgroup g) ∧
    Function.Surjective xi_terminal_zm_jg_wdn_forced_permutation_quotient ∧
    Fintype.card xi_terminal_zm_jg_demicube_32_vertex_set = 2 ^ (6 - 1)

/-- Paper label: `cor:xi-terminal-zm-jg-wdn-forced`. -/
theorem paper_xi_terminal_zm_jg_wdn_forced (D : xi_terminal_zm_jg_wdn_forced_data) :
    xi_terminal_zm_jg_wdn_forced_statement D := by
  rcases paper_xi_terminal_zm_jg_signed_permutation_representation with
    ⟨_, _, hinj, hweyl⟩
  rcases paper_xi_terminal_zm_jg_demicube_32 with ⟨hkernel, _⟩
  refine ⟨hinj, hweyl, xi_terminal_zm_jg_wdn_forced_permutation_quotient_surjective, ?_⟩
  simpa using hkernel

end Omega.Zeta
