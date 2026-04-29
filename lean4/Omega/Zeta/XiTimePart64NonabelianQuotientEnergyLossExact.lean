import Mathlib.Tactic
import Omega.Zeta.Arity335CharacterEnergy

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Visible quotient energy carried by the inflated channels. -/
noncomputable def xi_time_part64_nonabelian_quotient_energy_loss_exact_visibleEnergy
    (C : Fin 3 → Fin 3 → Fin 5 → ℂ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 5, if k.1 < 2 then ‖arity335CharacterCoeff C i j k‖ ^ 2 else 0

/-- Hidden energy carried by the non-inflated channels. -/
noncomputable def xi_time_part64_nonabelian_quotient_energy_loss_exact_hiddenEnergy
    (C : Fin 3 → Fin 3 → Fin 5 → ℂ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 5, if k.1 < 2 then 0 else ‖arity335CharacterCoeff C i j k‖ ^ 2

lemma xi_time_part64_nonabelian_quotient_energy_loss_exact_channel_split
    (C : Fin 3 → Fin 3 → Fin 5 → ℂ) :
    arity335CharacterEnergy C =
      xi_time_part64_nonabelian_quotient_energy_loss_exact_visibleEnergy C +
        xi_time_part64_nonabelian_quotient_energy_loss_exact_hiddenEnergy C := by
  simp [arity335CharacterEnergy,
    xi_time_part64_nonabelian_quotient_energy_loss_exact_visibleEnergy,
    xi_time_part64_nonabelian_quotient_energy_loss_exact_hiddenEnergy, Fin.sum_univ_three,
    Fin.sum_univ_five]
  ring

/-- Concrete proposition for
`thm:xi-time-part64-nonabelian-quotient-energy-loss-exact`. The centered channel decomposition
already gives the full Plancherel energy, splitting the first two channels as the visible
inflated quotient and the remaining three as the hidden non-inflated sector; subtracting the two
pieces records the exact energy loss. -/
def xi_time_part64_nonabelian_quotient_energy_loss_exact_statement : Prop :=
  ∀ C : Fin 3 → Fin 3 → Fin 5 → ℂ,
    arity335FrobeniusEnergy C =
        xi_time_part64_nonabelian_quotient_energy_loss_exact_visibleEnergy C +
          xi_time_part64_nonabelian_quotient_energy_loss_exact_hiddenEnergy C ∧
      arity335FrobeniusEnergy C -
          xi_time_part64_nonabelian_quotient_energy_loss_exact_visibleEnergy C =
        xi_time_part64_nonabelian_quotient_energy_loss_exact_hiddenEnergy C

lemma xi_time_part64_nonabelian_quotient_energy_loss_exact_statement_holds :
    xi_time_part64_nonabelian_quotient_energy_loss_exact_statement := by
  intro C
  have henergy := (paper_arity_335_character_energy C).2
  have hsplit := xi_time_part64_nonabelian_quotient_energy_loss_exact_channel_split C
  refine ⟨henergy.trans hsplit, ?_⟩
  rw [henergy, hsplit]
  ring

def paper_xi_time_part64_nonabelian_quotient_energy_loss_exact : Prop := by
  exact xi_time_part64_nonabelian_quotient_energy_loss_exact_statement

end

end Omega.Zeta
