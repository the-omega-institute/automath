import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.TqftGenusTowerCompleteMultiplicityInvariant

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite multiplicity data for the two-sided Mellin unification package. -/
structure ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData where
  conclusion_foldbin_multiplicity_mellin_two_sided_unification_window_size : ℕ
  conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity :
    Fin conclusion_foldbin_multiplicity_mellin_two_sided_unification_window_size → ℕ
  conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity_pos :
    ∀ x, 1 ≤ conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity x

/-- The multiplicity histogram attached to the fixed window. -/
def conclusion_foldbin_multiplicity_mellin_two_sided_unification_histogram
    (D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData) (d : ℕ) : ℕ :=
  Fintype.card
    {x :
        Fin D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_window_size //
      D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity x = d}

/-- Collision moments sampled on the positive Mellin side. -/
def conclusion_foldbin_multiplicity_mellin_two_sided_unification_collision_moment
    (D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData) (q : ℕ) : ℚ :=
  ∑ x, (D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity x : ℚ) ^ q

/-- Genus amplitudes sampled on the negative Mellin side through the atoms `d(x)^{-2}`. -/
def conclusion_foldbin_multiplicity_mellin_two_sided_unification_genus_amplitude
    (D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData) (g : ℕ) : ℚ :=
  ∑ x,
    (1 /
      (D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity x : ℚ) ^ 2) ^ g

/-- The Mellin-Dirichlet kernel, with the left side indexed by collision orders and the right side
by genus orders. -/
def conclusion_foldbin_multiplicity_mellin_two_sided_unification_kernel
    (D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData) : Sum ℕ ℕ → ℚ
  | Sum.inl q =>
      conclusion_foldbin_multiplicity_mellin_two_sided_unification_collision_moment D q
  | Sum.inr g =>
      conclusion_foldbin_multiplicity_mellin_two_sided_unification_genus_amplitude D g

/-- The paper-facing package: the same kernel recovers the collision moments and the genus
amplitudes on its two sides, and the genus tower carries the complete multiplicity data. -/
def ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData.Holds
    (D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData) : Prop :=
  (∀ q : ℕ,
    conclusion_foldbin_multiplicity_mellin_two_sided_unification_kernel D (Sum.inl q) =
      conclusion_foldbin_multiplicity_mellin_two_sided_unification_collision_moment D q) ∧
    (∀ g : ℕ,
      conclusion_foldbin_multiplicity_mellin_two_sided_unification_kernel D (Sum.inr g) =
        conclusion_foldbin_multiplicity_mellin_two_sided_unification_genus_amplitude D g) ∧
      conclusion_tqft_genus_tower_complete_multiplicity_invariant_statement
        D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity

/-- Paper label: `thm:conclusion-foldbin-multiplicity-mellin-two-sided-unification`. The same
finite Mellin kernel records the collision moments on one side and the genus amplitudes on the
other, while the already verified genus-tower reconstruction theorem recovers the full
multiplicity spectrum from those genus samples. -/
theorem paper_conclusion_foldbin_multiplicity_mellin_two_sided_unification
    (D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData) : D.Holds := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rfl
  · intro g
    rfl
  · exact
      paper_conclusion_tqft_genus_tower_complete_multiplicity_invariant
        D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity
        D.conclusion_foldbin_multiplicity_mellin_two_sided_unification_multiplicity_pos

end Omega.Conclusion
