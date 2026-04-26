import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Conclusion.FixedResolutionCollisionRationalHankelRank

namespace Omega.Conclusion

/-- The ordinary window-`6` support `{1,2,3,4,5}`. -/
def conclusion_window6_moment_tower_prony_rank_compression_ordinary_support : Fin 5 → ℚ :=
  fun i => (i.1 + 1 : ℚ)

/-- The ordinary window-`6` multiplicities `(2,4,8,5,2)`. -/
def conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights : Fin 5 → ℚ :=
  ![2, 4, 8, 5, 2]

/-- The binary window-`6` support `{2,3,4}`. -/
def conclusion_window6_moment_tower_prony_rank_compression_binary_support : Fin 3 → ℚ :=
  fun i => (i.1 + 2 : ℚ)

/-- The binary window-`6` multiplicities `(8,4,9)`. -/
def conclusion_window6_moment_tower_prony_rank_compression_binary_weights : Fin 3 → ℚ :=
  ![8, 4, 9]

/-- The ordinary moment tower `S_q^{ord}(6)`. -/
def conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q : ℕ) : ℚ :=
  fixedResolutionCollisionMoment
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights q

/-- The binary moment tower `S_q^{bin}(6)`. -/
def conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q : ℕ) : ℚ :=
  fixedResolutionCollisionMoment
    conclusion_window6_moment_tower_prony_rank_compression_binary_support
    conclusion_window6_moment_tower_prony_rank_compression_binary_weights q

/-- Paper-facing package for the explicit exponential sums, annihilating recurrences, and exact
Prony/Hankel ranks of the ordinary and binary window-`6` moment towers. -/
def conclusion_window6_moment_tower_prony_rank_compression_statement : Prop :=
  (∀ q : ℕ,
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment q =
        2 + 4 * 2 ^ q + 8 * 3 ^ q + 5 * 4 ^ q + 2 * 5 ^ q) ∧
    (∀ q : ℕ,
      conclusion_window6_moment_tower_prony_rank_compression_binary_moment q =
        8 * 2 ^ q + 4 * 3 ^ q + 9 * 4 ^ q) ∧
    (∀ q : ℕ,
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 5) =
        15 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 4) -
          85 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 3) +
          225 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 2) -
          274 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 1) +
          120 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment q) ∧
    (∀ q : ℕ,
      conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q + 3) =
        9 * conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q + 2) -
          26 * conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q + 1) +
          24 * conclusion_window6_moment_tower_prony_rank_compression_binary_moment q) ∧
    (∀ i j : ℕ,
      fixedResolutionCollisionHankelEntry
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights i j =
        fixedResolutionCollisionGramEntry
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights i j) ∧
    (∀ i j : ℕ,
      fixedResolutionCollisionHankelEntry
          conclusion_window6_moment_tower_prony_rank_compression_binary_support
          conclusion_window6_moment_tower_prony_rank_compression_binary_weights i j =
        fixedResolutionCollisionGramEntry
          conclusion_window6_moment_tower_prony_rank_compression_binary_support
          conclusion_window6_moment_tower_prony_rank_compression_binary_weights i j) ∧
    fixedResolutionCollisionDeterminantWitness
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights ∧
    fixedResolutionCollisionDeterminantWitness
      conclusion_window6_moment_tower_prony_rank_compression_binary_support
      conclusion_window6_moment_tower_prony_rank_compression_binary_weights ∧
    fixedResolutionCollisionExactHankelRank 5 ∧
    fixedResolutionCollisionExactHankelRank 3

private lemma conclusion_window6_moment_tower_prony_rank_compression_ordinary_formula
    (q : ℕ) :
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment q =
      2 + 4 * 2 ^ q + 8 * 3 ^ q + 5 * 4 ^ q + 2 * 5 ^ q := by
  rw [conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment,
    fixedResolutionCollisionMoment, Fin.sum_univ_five]
  simp [conclusion_window6_moment_tower_prony_rank_compression_ordinary_support,
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights]
  norm_num

private lemma conclusion_window6_moment_tower_prony_rank_compression_binary_formula (q : ℕ) :
    conclusion_window6_moment_tower_prony_rank_compression_binary_moment q =
      8 * 2 ^ q + 4 * 3 ^ q + 9 * 4 ^ q := by
  rw [conclusion_window6_moment_tower_prony_rank_compression_binary_moment,
    fixedResolutionCollisionMoment, Fin.sum_univ_three]
  simp [conclusion_window6_moment_tower_prony_rank_compression_binary_support,
    conclusion_window6_moment_tower_prony_rank_compression_binary_weights]
  norm_num

private lemma conclusion_window6_moment_tower_prony_rank_compression_ordinary_recurrence
    (q : ℕ) :
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 5) =
      15 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 4) -
        85 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 3) +
        225 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 2) -
        274 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment (q + 1) +
        120 * conclusion_window6_moment_tower_prony_rank_compression_ordinary_moment q := by
  repeat rw [conclusion_window6_moment_tower_prony_rank_compression_ordinary_formula]
  ring_nf

private lemma conclusion_window6_moment_tower_prony_rank_compression_binary_recurrence
    (q : ℕ) :
    conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q + 3) =
      9 * conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q + 2) -
        26 * conclusion_window6_moment_tower_prony_rank_compression_binary_moment (q + 1) +
        24 * conclusion_window6_moment_tower_prony_rank_compression_binary_moment q := by
  repeat rw [conclusion_window6_moment_tower_prony_rank_compression_binary_formula]
  ring_nf

private lemma conclusion_window6_moment_tower_prony_rank_compression_ordinary_support_strictMono :
    StrictMono conclusion_window6_moment_tower_prony_rank_compression_ordinary_support := by
  intro i j hij
  change ((i.1 + 1 : ℚ) < (j.1 + 1 : ℚ))
  exact_mod_cast Nat.succ_lt_succ hij

private lemma conclusion_window6_moment_tower_prony_rank_compression_binary_support_strictMono :
    StrictMono conclusion_window6_moment_tower_prony_rank_compression_binary_support := by
  intro i j hij
  change ((i.1 + 2 : ℚ) < (j.1 + 2 : ℚ))
  exact_mod_cast Nat.add_lt_add_right hij 2

private lemma conclusion_window6_moment_tower_prony_rank_compression_ordinary_weight_nonzero
    (i : Fin 5) :
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights i ≠ 0 := by
  fin_cases i <;> simp [conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights]

private lemma conclusion_window6_moment_tower_prony_rank_compression_binary_weight_nonzero
    (i : Fin 3) :
    conclusion_window6_moment_tower_prony_rank_compression_binary_weights i ≠ 0 := by
  fin_cases i <;> simp [conclusion_window6_moment_tower_prony_rank_compression_binary_weights]

private lemma conclusion_window6_moment_tower_prony_rank_compression_ordinary_hankel_package :
    (∀ i j : ℕ,
      fixedResolutionCollisionHankelEntry
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights i j =
        fixedResolutionCollisionGramEntry
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
          conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights i j) ∧
      fixedResolutionCollisionDeterminantWitness
        conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
        conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights ∧
      fixedResolutionCollisionExactHankelRank 5 := by
  have hpack :=
    paper_conclusion_fixedresolution_collision_rational_hankel_rank 5 0
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_support
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_weights 0
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_support_strictMono
      conclusion_window6_moment_tower_prony_rank_compression_ordinary_weight_nonzero
      (by intro i; simp)
  rcases hpack with ⟨_, hHankel, hDet, hRank⟩
  exact ⟨hHankel, hDet, hRank⟩

private lemma conclusion_window6_moment_tower_prony_rank_compression_binary_hankel_package :
    (∀ i j : ℕ,
      fixedResolutionCollisionHankelEntry
          conclusion_window6_moment_tower_prony_rank_compression_binary_support
          conclusion_window6_moment_tower_prony_rank_compression_binary_weights i j =
        fixedResolutionCollisionGramEntry
          conclusion_window6_moment_tower_prony_rank_compression_binary_support
          conclusion_window6_moment_tower_prony_rank_compression_binary_weights i j) ∧
      fixedResolutionCollisionDeterminantWitness
        conclusion_window6_moment_tower_prony_rank_compression_binary_support
        conclusion_window6_moment_tower_prony_rank_compression_binary_weights ∧
      fixedResolutionCollisionExactHankelRank 3 := by
  have hpack :=
    paper_conclusion_fixedresolution_collision_rational_hankel_rank 3 0
      conclusion_window6_moment_tower_prony_rank_compression_binary_support
      conclusion_window6_moment_tower_prony_rank_compression_binary_weights 0
      conclusion_window6_moment_tower_prony_rank_compression_binary_support_strictMono
      conclusion_window6_moment_tower_prony_rank_compression_binary_weight_nonzero
      (by intro i; simp)
  rcases hpack with ⟨_, hHankel, hDet, hRank⟩
  exact ⟨hHankel, hDet, hRank⟩

/-- Paper label: `thm:conclusion-window6-moment-tower-prony-rank-compression`. The ordinary and
binary window-`6` moment towers are explicit finite exponential sums with annihilating
recurrences coming from `(E - 1)(E - 2)(E - 3)(E - 4)(E - 5)` and `(E - 2)(E - 3)(E - 4)`;
their Hankel/Prony ranks are exactly `5` and `3`. -/
theorem paper_conclusion_window6_moment_tower_prony_rank_compression :
    conclusion_window6_moment_tower_prony_rank_compression_statement := by
  rcases conclusion_window6_moment_tower_prony_rank_compression_ordinary_hankel_package with
    ⟨hOrdHankel, hOrdDet, hOrdRank⟩
  rcases conclusion_window6_moment_tower_prony_rank_compression_binary_hankel_package with
    ⟨hBinHankel, hBinDet, hBinRank⟩
  refine ⟨conclusion_window6_moment_tower_prony_rank_compression_ordinary_formula,
    conclusion_window6_moment_tower_prony_rank_compression_binary_formula,
    conclusion_window6_moment_tower_prony_rank_compression_ordinary_recurrence,
    conclusion_window6_moment_tower_prony_rank_compression_binary_recurrence,
    hOrdHankel, hBinHankel, hOrdDet, hBinDet, hOrdRank, hBinRank⟩

end Omega.Conclusion
