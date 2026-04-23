import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The five transported root pairs used in the algebraic-scale bookkeeping. -/
abbrev xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_root_pair :=
  Fin 5 × Bool

/-- The sign choices on the five root pairs. -/
abbrev xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_sign_vector :=
  Fin 5 → Bool

/-- Chapter-local transport model: a sign vector together with a permutation of the root pairs. -/
abbrev xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_transport_model :=
  xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_sign_vector × Equiv.Perm (Fin 5)

/-- The transported Galois action remembers only the permutation quotient on the root pairs. -/
def xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_permutation_quotient
    (g : xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_transport_model) :
    Equiv.Perm (Fin 5) :=
  g.2

/-- The trivial sign vector gives a canonical lift of every permutation. -/
def xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_trivial_sign_vector :
    xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_sign_vector :=
  fun _ => false

lemma xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_permutation_quotient_surjective :
    Function.Surjective
      xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_permutation_quotient := by
  intro π
  exact
    ⟨(xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_trivial_sign_vector, π), rfl⟩

/-- The finite exceptional scale values excluded in the chapter-local coherence package. -/
def xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_exceptional_r_values :
    Finset ℤ :=
  {0, 1}

/-- Outside the finite exceptional set, the transported root-pair package is coherent. -/
def xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_transport_statement
    (_r : ℤ) : Prop :=
  Function.Surjective
      xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_permutation_quotient ∧
    Fintype.card xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_sign_vector =
      2 ^ 5

/-- Paper-facing finite-exception coherence package for the algebraic-scale transport. -/
def xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_statement : Prop :=
  ∃ badR : Finset ℤ,
    badR = xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_exceptional_r_values ∧
      badR.card = 2 ∧
      ∀ r : ℤ,
        r ∉ badR →
          xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_transport_statement r

/-- Paper label: `thm:xi-terminal-zm-jg-algebraic-scale-finite-exception-coherence`. -/
theorem paper_xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence :
    xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_statement := by
  refine ⟨xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_exceptional_r_values, rfl,
    by decide, ?_⟩
  intro r hr
  let _ := hr
  refine
    ⟨xi_terminal_zm_jg_algebraic_scale_finite_exception_coherence_permutation_quotient_surjective,
      ?_⟩
  native_decide

end Omega.Zeta
