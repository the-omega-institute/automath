import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-order expansion certificate for BBP/Bellard/spigot tails.  A fixed finite
window is represented by a finite type, its coefficients, and the moment coefficients that appear
in each asymptotic order. -/
structure conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_data where
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowSize : ℕ
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_order : ℕ
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder : ℕ
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowCoeff :
    Fin conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowSize → ℝ
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_tailMoment :
    ℕ → Fin conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowSize → ℝ
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff :
    ℕ → ℝ
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansion :
    ∀ ν, ν ≤ conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_order →
      conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff ν =
        ∑ j,
          conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowCoeff j *
            conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_tailMoment ν j
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_le_order :
    conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder ≤
      conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_order
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_vanish_before :
    ∀ ν, ν < conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder →
      ∑ j,
        conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowCoeff j *
          conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_tailMoment ν j = 0
  conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_nonzero :
    ∑ j,
      conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowCoeff j *
        conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_tailMoment
          conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder j ≠ 0

/-- The fixed-window coefficient at one asymptotic order. -/
def conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_window_combination
    (D : conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_data)
    (ν : ℕ) : ℝ :=
  ∑ j,
    D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_windowCoeff j *
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_tailMoment ν j

/-- The expansion certificate at order `ν`. -/
def conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansion_predicate
    (D : conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_data)
    (ν : ℕ) : Prop :=
  D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff ν =
    conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_window_combination D ν

/-- Inductively propagate the vanishing of all lower-order fixed-window coefficients. -/
lemma conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_vanish_by_induction
    (D : conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_data) :
    ∀ m,
      m ≤ D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder →
        ∀ ν, ν < m →
          D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff ν =
            0 := by
  intro m hm
  induction m with
  | zero =>
      intro ν hν
      exact (Nat.not_lt_zero ν hν).elim
  | succ m ih =>
      intro ν hν
      have hν_first :
          ν <
            D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder :=
        lt_of_lt_of_le hν hm
      rw [D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansion ν
        (le_trans (le_of_lt hν_first)
          D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_le_order)]
      simpa [conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_window_combination]
        using
          D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_vanish_before ν
            hν_first

/-- Paper-facing obstruction package: below the first nonzero window coefficient all expansion
orders vanish, while the first order gives a certified nonzero algebraic-exponential tail term. -/
def conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_statement
    (D : conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_data) : Prop :=
  (∀ ν,
      ν < D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder →
        D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff ν =
          0) ∧
    D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder ≤
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_order ∧
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff
          D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder ≠ 0 ∧
        ∃ ν,
          ν ≤ D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_order ∧
            D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansionCoeff ν
              ≠ 0

/-- Paper label: `thm:conclusion-foldgauge-pi-bbp-tail-algebraic-exponential-obstruction`. -/
theorem paper_conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction
    (D : conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_data) :
    conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_statement D := by
  refine ⟨?_, D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_le_order,
    ?_, ?_⟩
  · exact
      conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_vanish_by_induction D
        D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder
        le_rfl
  · rw [D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansion
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_le_order]
    simpa [conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_window_combination]
      using
        D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_nonzero
  · refine
      ⟨D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder,
        D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_le_order,
        ?_⟩
    rw [D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_expansion
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_firstOrder
      D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_le_order]
    simpa [conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_window_combination]
      using
        D.conclusion_foldgauge_pi_bbp_tail_algebraic_exponential_obstruction_first_nonzero

end Omega.Conclusion
