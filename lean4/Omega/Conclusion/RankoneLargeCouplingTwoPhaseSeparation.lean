import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete rank-one secular-equation data for the large-coupling two-phase separation audit. -/
structure conclusion_rankone_large_coupling_two_phase_separation_data where
  conclusion_rankone_large_coupling_two_phase_separation_q : ℕ
  conclusion_rankone_large_coupling_two_phase_separation_pole :
    Fin (conclusion_rankone_large_coupling_two_phase_separation_q + 1) → ℝ
  conclusion_rankone_large_coupling_two_phase_separation_weight :
    Fin (conclusion_rankone_large_coupling_two_phase_separation_q + 1) → ℝ
  conclusion_rankone_large_coupling_two_phase_separation_root :
    Fin conclusion_rankone_large_coupling_two_phase_separation_q → ℝ
  conclusion_rankone_large_coupling_two_phase_separation_lowerBranch :
    ℝ → Fin conclusion_rankone_large_coupling_two_phase_separation_q → ℝ
  conclusion_rankone_large_coupling_two_phase_separation_upperBranch :
    ℝ → Fin conclusion_rankone_large_coupling_two_phase_separation_q → ℝ
  conclusion_rankone_large_coupling_two_phase_separation_threshold : ℝ
  conclusion_rankone_large_coupling_two_phase_separation_orderedPoles :
    ∀ i j : Fin (conclusion_rankone_large_coupling_two_phase_separation_q + 1),
      (i : ℕ) < (j : ℕ) →
        conclusion_rankone_large_coupling_two_phase_separation_pole i <
          conclusion_rankone_large_coupling_two_phase_separation_pole j
  conclusion_rankone_large_coupling_two_phase_separation_positiveWeights :
    ∀ i, 0 < conclusion_rankone_large_coupling_two_phase_separation_weight i
  conclusion_rankone_large_coupling_two_phase_separation_interlacingRoots :
    ∀ j : Fin conclusion_rankone_large_coupling_two_phase_separation_q,
      conclusion_rankone_large_coupling_two_phase_separation_pole j.castSucc <
          conclusion_rankone_large_coupling_two_phase_separation_root j ∧
        conclusion_rankone_large_coupling_two_phase_separation_root j <
          conclusion_rankone_large_coupling_two_phase_separation_pole j.succ
  conclusion_rankone_large_coupling_two_phase_separation_lowerAsymptotic :
    ∀ b, conclusion_rankone_large_coupling_two_phase_separation_threshold ≤ b →
      ∀ j, conclusion_rankone_large_coupling_two_phase_separation_lowerBranch b j <
        conclusion_rankone_large_coupling_two_phase_separation_root j
  conclusion_rankone_large_coupling_two_phase_separation_upperAsymptotic :
    ∀ b, conclusion_rankone_large_coupling_two_phase_separation_threshold ≤ b →
      ∀ j, conclusion_rankone_large_coupling_two_phase_separation_root j <
        conclusion_rankone_large_coupling_two_phase_separation_upperBranch b j

namespace conclusion_rankone_large_coupling_two_phase_separation_data

/-- Total rank-one weight. -/
noncomputable def totalWeight
    (D : conclusion_rankone_large_coupling_two_phase_separation_data) : ℝ :=
  ∑ i, D.conclusion_rankone_large_coupling_two_phase_separation_weight i

/-- Ordered-pole audit predicate. -/
def orderedPoleAudit
    (D : conclusion_rankone_large_coupling_two_phase_separation_data) : Prop :=
  ∀ i j : Fin (D.conclusion_rankone_large_coupling_two_phase_separation_q + 1),
    (i : ℕ) < (j : ℕ) →
      D.conclusion_rankone_large_coupling_two_phase_separation_pole i <
        D.conclusion_rankone_large_coupling_two_phase_separation_pole j

/-- Interlacing audit predicate for the `q` exceptional roots. -/
def interlacingAudit
    (D : conclusion_rankone_large_coupling_two_phase_separation_data) : Prop :=
  ∀ j : Fin D.conclusion_rankone_large_coupling_two_phase_separation_q,
    D.conclusion_rankone_large_coupling_two_phase_separation_pole j.castSucc <
        D.conclusion_rankone_large_coupling_two_phase_separation_root j ∧
      D.conclusion_rankone_large_coupling_two_phase_separation_root j <
        D.conclusion_rankone_large_coupling_two_phase_separation_pole j.succ

/-- Large-coupling branch separation audit predicate. -/
def branchSeparationAudit
    (D : conclusion_rankone_large_coupling_two_phase_separation_data) : Prop :=
  ∀ b, D.conclusion_rankone_large_coupling_two_phase_separation_threshold ≤ b →
    ∀ j : Fin D.conclusion_rankone_large_coupling_two_phase_separation_q,
      D.conclusion_rankone_large_coupling_two_phase_separation_lowerBranch b j <
          D.conclusion_rankone_large_coupling_two_phase_separation_root j ∧
        D.conclusion_rankone_large_coupling_two_phase_separation_root j <
          D.conclusion_rankone_large_coupling_two_phase_separation_upperBranch b j

/-- Packaged two-phase separation conclusion: positive total coupling weight, ordered poles,
interlacing roots, and separated lower/upper large-coupling branches. -/
def twoPhaseSeparation
    (D : conclusion_rankone_large_coupling_two_phase_separation_data) : Prop :=
  0 < D.totalWeight ∧ D.orderedPoleAudit ∧ D.interlacingAudit ∧ D.branchSeparationAudit

end conclusion_rankone_large_coupling_two_phase_separation_data

/-- Paper label: `thm:conclusion-rankone-large-coupling-two-phase-separation`. -/
theorem paper_conclusion_rankone_large_coupling_two_phase_separation
    (D : conclusion_rankone_large_coupling_two_phase_separation_data) :
    D.twoPhaseSeparation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [conclusion_rankone_large_coupling_two_phase_separation_data.totalWeight]
    have hterm :
        ∀ i : Fin (D.conclusion_rankone_large_coupling_two_phase_separation_q + 1),
          0 < D.conclusion_rankone_large_coupling_two_phase_separation_weight i :=
      D.conclusion_rankone_large_coupling_two_phase_separation_positiveWeights
    have hnonempty :
        (Finset.univ :
          Finset (Fin (D.conclusion_rankone_large_coupling_two_phase_separation_q + 1))).Nonempty :=
      ⟨⟨0, Nat.succ_pos D.conclusion_rankone_large_coupling_two_phase_separation_q⟩, by simp⟩
    exact Finset.sum_pos (fun i _hi => hterm i) hnonempty
  · intro i j hij
    exact D.conclusion_rankone_large_coupling_two_phase_separation_orderedPoles i j hij
  · intro j
    exact D.conclusion_rankone_large_coupling_two_phase_separation_interlacingRoots j
  · intro b hb j
    exact ⟨D.conclusion_rankone_large_coupling_two_phase_separation_lowerAsymptotic b hb j,
      D.conclusion_rankone_large_coupling_two_phase_separation_upperAsymptotic b hb j⟩

end Omega.Conclusion
