import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete window-6 reachability data for
`thm:xi-time-part9zn-window6-cyclic-boundary-noninvariance-reachability`. -/
structure xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_data where
  reachable : Fin 21 → Fin 21 → Prop
  matrix_units_generate_reachability : ∀ u v : Fin 21, reachable u v
  invariant_simplicity :
    ∀ S : Finset (Fin 21),
      (∀ u, u ∈ S → ∀ v, reachable u v → v ∈ S) → S.Nonempty → S = Finset.univ

def xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_invariant
    (D : xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_data)
    (S : Finset (Fin 21)) : Prop :=
  S.Nonempty ∧ ∀ u, u ∈ S → ∀ v, D.reachable u v → v ∈ S

def xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_statement
    (D : xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_data) : Prop :=
  (¬ ∃ S : Finset (Fin 21), S.card = 18 ∧
    xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_invariant D S) ∧
  (¬ ∃ S : Finset (Fin 21), S.card = 3 ∧
    xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_invariant D S) ∧
  (∀ u v : Fin 21, D.reachable u v) ∧
  (∀ b c : Fin 21, b.val < 3 → 3 ≤ c.val → D.reachable b c ∧ D.reachable c b)

/-- Paper label:
`thm:xi-time-part9zn-window6-cyclic-boundary-noninvariance-reachability`. -/
theorem paper_xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability
    (D : xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_data) :
    xi_time_part9zn_window6_cyclic_boundary_noninvariance_reachability_statement D := by
  refine ⟨?_, ?_, D.matrix_units_generate_reachability, ?_⟩
  · rintro ⟨S, hcard, hnonempty, hclosed⟩
    have hS : S = Finset.univ := D.invariant_simplicity S hclosed hnonempty
    rw [hS] at hcard
    simp at hcard
  · rintro ⟨S, hcard, hnonempty, hclosed⟩
    have hS : S = Finset.univ := D.invariant_simplicity S hclosed hnonempty
    rw [hS] at hcard
    simp at hcard
  · intro b c _ _
    exact ⟨D.matrix_units_generate_reachability b c,
      D.matrix_units_generate_reachability c b⟩

end Omega.Zeta
