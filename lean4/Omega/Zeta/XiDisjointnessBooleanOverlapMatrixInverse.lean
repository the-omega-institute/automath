import Omega.Zeta.BooleanDisjointnessZetaLDLT
import Omega.Zeta.XiBooleanTwoLayerSymmetricQuotientInverse

namespace Omega.Zeta

open scoped BigOperators

/-- Label-prefixed nonempty Boolean subsets used for the overlap block. -/
abbrev xi_disjointness_boolean_overlap_matrix_inverse_nonempty_subset (q : ℕ) :=
  {U : Finset (Fin q) // U.Nonempty}

/-- The nonempty-overlap matrix entry on the nonempty Boolean layer. -/
def xi_disjointness_boolean_overlap_matrix_inverse_overlap_entry (q : ℕ)
    (U V : xi_disjointness_boolean_overlap_matrix_inverse_nonempty_subset q) : ℤ :=
  if (U.1 ∩ V.1).Nonempty then 1 else 0

/-- The proposed integer inverse entry: it is supported exactly on covering pairs. -/
def xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry (q : ℕ)
    (U V : xi_disjointness_boolean_overlap_matrix_inverse_nonempty_subset q) : ℤ :=
  if U.1 ∪ V.1 = Finset.univ then
    (-1 : ℤ) ^ ((U.1 ∩ V.1).card + 1)
  else
    0

lemma xi_disjointness_boolean_overlap_matrix_inverse_neg_one_pow_mem (n : ℕ) :
    (-1 : ℤ) ^ n ∈ ({-1, 0, 1} : Finset ℤ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      have hcases : (-1 : ℤ) ^ n = -1 ∨ (-1 : ℤ) ^ n = 0 ∨ (-1 : ℤ) ^ n = 1 := by
        simpa using ih
      rcases hcases with h | h | h <;> simp [h]

lemma xi_disjointness_boolean_overlap_matrix_inverse_neg_one_pow_ne_zero (n : ℕ) :
    (-1 : ℤ) ^ n ≠ 0 :=
  pow_ne_zero n (by norm_num)

/-- Concrete support formula for the lower-right inverse block. -/
def xi_disjointness_boolean_overlap_matrix_inverse_support_statement (q : ℕ) : Prop :=
  ∀ U V : xi_disjointness_boolean_overlap_matrix_inverse_nonempty_subset q,
    xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry q U V ∈
        ({-1, 0, 1} : Finset ℤ) ∧
      (xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry q U V ≠ 0 ↔
        U.1 ∪ V.1 = Finset.univ)

/-- Concrete statement combining the Boolean zeta factorization with the inverse support block. -/
def xi_disjointness_boolean_overlap_matrix_inverse_statement (q : ℕ) : Prop :=
  booleanDisjointnessZetaFactorization q ∧
    booleanDisjointnessMobiusCongruence q ∧
    xi_disjointness_boolean_overlap_matrix_inverse_support_statement q

/-- Paper label: `prop:xi-disjointness-boolean-overlap-matrix-inverse`. -/
theorem paper_xi_disjointness_boolean_overlap_matrix_inverse (q : ℕ) (hq : 2 ≤ q) :
    xi_disjointness_boolean_overlap_matrix_inverse_statement q := by
  rcases paper_xi_disjointness_boolean_zeta_ldlt q hq with ⟨hzeta, hmobius⟩
  refine ⟨hzeta, hmobius, ?_⟩
  intro U V
  by_cases hcover : U.1 ∪ V.1 = Finset.univ
  · constructor
    · simpa [xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry, hcover] using
        xi_disjointness_boolean_overlap_matrix_inverse_neg_one_pow_mem ((U.1 ∩ V.1).card + 1)
    · simp [xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry, hcover,
        xi_disjointness_boolean_overlap_matrix_inverse_neg_one_pow_ne_zero ((U.1 ∩ V.1).card + 1)]
  · constructor
    · simp [xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry, hcover]
    · simp [xi_disjointness_boolean_overlap_matrix_inverse_inverse_entry, hcover]

end Omega.Zeta
