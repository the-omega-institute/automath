import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch
import Omega.Conclusion.Window6NoLinearFactorization

namespace Omega.Conclusion

/-- Minimal seed: finite reduced root systems come in opposite pairs, so only even cardinalities
are allowed. -/
def conclusion_window6_not_root_system_not_free_quotient_finite_reduced_root_system_cardinality
    (card : ℕ) : Prop :=
  Even card

/-- The whole `21`-point window-`6` space cannot be a finite reduced root system. -/
def conclusion_window6_not_root_system_not_free_quotient_whole_space_obstruction : Prop :=
  ¬ conclusion_window6_not_root_system_not_free_quotient_finite_reduced_root_system_cardinality 21

/-- Nor can the `18` visible directions be enlarged by exactly `3` extra points to a finite
reduced root system. -/
def conclusion_window6_not_root_system_not_free_quotient_extension_obstruction : Prop :=
  ¬ ∃ card : ℕ,
      conclusion_window6_not_root_system_not_free_quotient_finite_reduced_root_system_cardinality
        card ∧
        card = 18 + 3

/-- The established free-orbit and affine-coset obstructions for the window-`6` quotient. -/
def conclusion_window6_not_root_system_not_free_quotient_groupoid_obstruction : Prop :=
  full_fiber_partition_is_not_a_free_finite_group_orbit_partition ∧
    ¬ ∃ k, Omega.GU.TerminalFoldbin6CosetModel k

lemma conclusion_window6_not_root_system_not_free_quotient_cardinality_even {card : ℕ}
    (hcard :
      conclusion_window6_not_root_system_not_free_quotient_finite_reduced_root_system_cardinality
        card) :
    Even card := hcard

/-- Paper label: `prop:conclusion-window6-not-root-system-not-free-quotient`. The odd cardinality
`21 = 18 + 3` rules out both the whole-space and the three-point-extension root-system scenarios,
while the existing window-`6` quotient certificates already exclude free finite-group orbits and
affine-coset models. -/
theorem paper_conclusion_window6_not_root_system_not_free_quotient :
    conclusion_window6_not_root_system_not_free_quotient_whole_space_obstruction ∧
      conclusion_window6_not_root_system_not_free_quotient_extension_obstruction ∧
      conclusion_window6_not_root_system_not_free_quotient_groupoid_obstruction := by
  refine ⟨?_, ?_, ?_⟩
  · intro hroot
    rcases
      conclusion_window6_not_root_system_not_free_quotient_cardinality_even hroot with
      ⟨k, hk⟩
    omega
  · intro hext
    rcases hext with ⟨card, hcard, hcard_eq⟩
    have h21 : Even 21 := by
      simpa [hcard_eq] using
        conclusion_window6_not_root_system_not_free_quotient_cardinality_even hcard
    rcases h21 with ⟨k, hk⟩
    omega
  · rcases paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch with ⟨_, hfree⟩
    exact ⟨hfree, paper_conclusion_window6_no_linear_factorization⟩

end Omega.Conclusion
