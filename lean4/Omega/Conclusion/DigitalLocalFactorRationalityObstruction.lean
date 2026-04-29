import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic

open scoped Classical

namespace Omega.Conclusion

/-- Pole set contributed by the nontrivial local factors. -/
def conclusion_digital_local_factor_rationality_obstruction_pole_set
    (M : ℕ → Finset ℂ) : Set ℂ :=
  {z | ∃ k, z ∈ M k}

/-- Indices whose local factor has a pole at `z`. -/
def conclusion_digital_local_factor_rationality_obstruction_pole_indices
    (M : ℕ → Finset ℂ) (z : ℂ) : Set ℕ :=
  {k | z ∈ M k}

/-- Nontrivial local factors. -/
def conclusion_digital_local_factor_rationality_obstruction_active_indices
    (M : ℕ → Finset ℂ) : Set ℕ :=
  {k | (M k).Nonempty}

/-- All poles lie on the unit circle. -/
def conclusion_digital_local_factor_rationality_obstruction_unit_circle_spectrum
    (M : ℕ → Finset ℂ) : Prop :=
  ∀ k z, z ∈ M k → ‖z‖ = 1

/-- Rational admissibility means that only finitely many distinct poles can appear and that each
individual pole occurs in only finitely many factors. -/
def conclusion_digital_local_factor_rationality_obstruction_rational_admissible
    (M : ℕ → Finset ℂ) : Prop :=
  (conclusion_digital_local_factor_rationality_obstruction_pole_set M).Finite ∧
    ∀ z ∈ conclusion_digital_local_factor_rationality_obstruction_pole_set M,
      (conclusion_digital_local_factor_rationality_obstruction_pole_indices M z).Finite

/-- Paper label: `prop:conclusion-digital-local-factor-rationality-obstruction`. In the concrete
pole model, rational admissibility is equivalent to having only finitely many nontrivial local
factors. This is the set-theoretic core of the “infinitely many poles or unbounded order”
obstruction. -/
theorem paper_conclusion_digital_local_factor_rationality_obstruction
    (M : ℕ → Finset ℂ)
    (_hunit : conclusion_digital_local_factor_rationality_obstruction_unit_circle_spectrum M) :
    conclusion_digital_local_factor_rationality_obstruction_rational_admissible M ↔
      (conclusion_digital_local_factor_rationality_obstruction_active_indices M).Finite := by
  constructor
  · rintro ⟨hpoles, hmult⟩
    refine Set.Finite.subset (Set.Finite.biUnion hpoles hmult) ?_
    intro k hk
    rcases hk with ⟨z, hz⟩
    exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨⟨k, hz⟩, hz⟩⟩
  · intro hactive
    refine ⟨?_, ?_⟩
    · refine Set.Finite.subset (Set.Finite.biUnion hactive fun k _ => Finset.finite_toSet (M k)) ?_
      intro z hz
      rcases hz with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨⟨z, hk⟩, by simpa using hk⟩⟩
    · intro z hz
      refine Set.Finite.subset hactive ?_
      intro k hk
      exact ⟨z, hk⟩

end Omega.Conclusion
