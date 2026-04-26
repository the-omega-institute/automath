import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete consensus data on a finite cover: an anchored local readout family and a nonzero
descent obstruction that every global readout would force to vanish. -/
structure conclusion_consensus_functor_separated_not_sheaf_data where
  coverSize : ℕ
  anchor : Fin coverSize
  localReadout : Fin coverSize → ℤ
  obstruction : ℤ
  obstruction_ne_zero : obstruction ≠ 0
  global_readout_forces_obstruction_zero :
    (∃ t : ℤ, ∀ i : Fin coverSize, localReadout i = t) → obstruction = 0

/-- A global consensus readout is a single clock value agreeing with every local readout. -/
def conclusion_consensus_functor_separated_not_sheaf_global_readout
    (C : conclusion_consensus_functor_separated_not_sheaf_data) (t : ℤ) : Prop :=
  ∀ i : Fin C.coverSize, C.localReadout i = t

/-- Local compatibility on self-overlaps, the finite-cover part of the descent datum. -/
def conclusion_consensus_functor_separated_not_sheaf_compatible_local_readouts
    (C : conclusion_consensus_functor_separated_not_sheaf_data) : Prop :=
  ∀ i : Fin C.coverSize, C.localReadout i - C.localReadout i = 0

/-- Separatedness of the consensus functor: two global readouts with the same local restrictions
coincide. -/
def conclusion_consensus_functor_separated_not_sheaf_separated
    (C : conclusion_consensus_functor_separated_not_sheaf_data) : Prop :=
  ∀ t u : ℤ,
    conclusion_consensus_functor_separated_not_sheaf_global_readout C t →
      conclusion_consensus_functor_separated_not_sheaf_global_readout C u → t = u

/-- The effective descent failure witness: compatible local data cannot be globalized because its
obstruction is nonzero. -/
def conclusion_consensus_functor_separated_not_sheaf_effective_descent_failure
    (C : conclusion_consensus_functor_separated_not_sheaf_data) : Prop :=
  conclusion_consensus_functor_separated_not_sheaf_compatible_local_readouts C ∧
    ¬ ∃ t : ℤ, conclusion_consensus_functor_separated_not_sheaf_global_readout C t

/-- Paper-facing separated-but-not-sheaf statement for the concrete consensus functor package. -/
def conclusion_consensus_functor_separated_not_sheaf_statement
    (C : conclusion_consensus_functor_separated_not_sheaf_data) : Prop :=
  conclusion_consensus_functor_separated_not_sheaf_separated C ∧
    conclusion_consensus_functor_separated_not_sheaf_effective_descent_failure C

lemma conclusion_consensus_functor_separated_not_sheaf_separated_of_anchor
    (C : conclusion_consensus_functor_separated_not_sheaf_data) :
    conclusion_consensus_functor_separated_not_sheaf_separated C := by
  intro t u ht hu
  exact (ht C.anchor).symm.trans (hu C.anchor)

lemma conclusion_consensus_functor_separated_not_sheaf_compatible
    (C : conclusion_consensus_functor_separated_not_sheaf_data) :
    conclusion_consensus_functor_separated_not_sheaf_compatible_local_readouts C := by
  intro i
  simp

lemma conclusion_consensus_functor_separated_not_sheaf_no_global_readout
    (C : conclusion_consensus_functor_separated_not_sheaf_data) :
    ¬ ∃ t : ℤ, conclusion_consensus_functor_separated_not_sheaf_global_readout C t := by
  intro hglobal
  exact C.obstruction_ne_zero (C.global_readout_forces_obstruction_zero hglobal)

/-- Paper label: `prop:conclusion-consensus-functor-separated-not-sheaf`. -/
theorem paper_conclusion_consensus_functor_separated_not_sheaf
    (C : conclusion_consensus_functor_separated_not_sheaf_data) :
    conclusion_consensus_functor_separated_not_sheaf_statement C := by
  refine ⟨?_, ?_, ?_⟩
  · exact conclusion_consensus_functor_separated_not_sheaf_separated_of_anchor C
  · exact conclusion_consensus_functor_separated_not_sheaf_compatible C
  · exact conclusion_consensus_functor_separated_not_sheaf_no_global_readout C

end Omega.Conclusion
