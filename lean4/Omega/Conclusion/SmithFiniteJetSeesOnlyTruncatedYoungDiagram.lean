import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite Smith jet at cutoff `K`: the profile records the sums of
`min k e_i` for `0 ≤ k ≤ K`. -/
def conclusion_smith_finite_jet_sees_only_truncated_young_diagram_jet
    (K : ℕ) {m : ℕ} (exponents : Fin m → ℕ) : Fin (K + 1) → ℕ :=
  fun k => ∑ i : Fin m, min k.val (exponents i)

/-- Input package for the finite-jet blindness statement. It stores a finite
p-primary exponent list together with one tail exponent strictly above the cutoff. -/
structure conclusion_smith_finite_jet_sees_only_truncated_young_diagram_data where
  width : ℕ
  cutoff : ℕ
  exponents : Fin width → ℕ
  tailIndex : Fin width
  tailAboveCutoff : cutoff < exponents tailIndex

/-- Replace the chosen tail exponent by `e + r`, leaving every other exponent unchanged. -/
def conclusion_smith_finite_jet_sees_only_truncated_young_diagram_tail_replace
    (D : conclusion_smith_finite_jet_sees_only_truncated_young_diagram_data) (r : ℕ) :
    Fin D.width → ℕ :=
  fun i => if i = D.tailIndex then D.exponents i + r else D.exponents i

/-- The paper statement: every upward tail perturbation has a concrete exponent witness
with exactly the same finite jet through the cutoff. -/
def conclusion_smith_finite_jet_sees_only_truncated_young_diagram_data.statement
    (D : conclusion_smith_finite_jet_sees_only_truncated_young_diagram_data) : Prop :=
  ∀ r : ℕ,
    ∃ exponents' : Fin D.width → ℕ,
      exponents' =
          conclusion_smith_finite_jet_sees_only_truncated_young_diagram_tail_replace D r ∧
        conclusion_smith_finite_jet_sees_only_truncated_young_diagram_jet D.cutoff
            exponents' =
          conclusion_smith_finite_jet_sees_only_truncated_young_diagram_jet D.cutoff
            D.exponents ∧
        exponents' D.tailIndex = D.exponents D.tailIndex + r

/-- prop:conclusion-smith-finite-jet-sees-only-truncated-young-diagram -/
theorem paper_conclusion_smith_finite_jet_sees_only_truncated_young_diagram
    (D : conclusion_smith_finite_jet_sees_only_truncated_young_diagram_data) :
    D.statement := by
  intro r
  refine
    ⟨conclusion_smith_finite_jet_sees_only_truncated_young_diagram_tail_replace D r, rfl,
      ?_, ?_⟩
  · funext k
    simp only [conclusion_smith_finite_jet_sees_only_truncated_young_diagram_jet]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases h : i = D.tailIndex
    · subst i
      have hk_cutoff : k.val ≤ D.cutoff := Nat.le_of_lt_succ k.isLt
      have hk_tail : k.val ≤ D.exponents D.tailIndex :=
        le_trans hk_cutoff (Nat.le_of_lt D.tailAboveCutoff)
      have hk_tail_r : k.val ≤ D.exponents D.tailIndex + r :=
        le_trans hk_tail (Nat.le_add_right _ _)
      have hleft :
          min k.val (D.exponents D.tailIndex + r) = k.val := Nat.min_eq_left hk_tail_r
      have hright : min k.val (D.exponents D.tailIndex) = k.val := Nat.min_eq_left hk_tail
      simp [conclusion_smith_finite_jet_sees_only_truncated_young_diagram_tail_replace,
        hleft, hright]
    · simp [conclusion_smith_finite_jet_sees_only_truncated_young_diagram_tail_replace, h]
  · simp [conclusion_smith_finite_jet_sees_only_truncated_young_diagram_tail_replace]

end Omega.Conclusion
