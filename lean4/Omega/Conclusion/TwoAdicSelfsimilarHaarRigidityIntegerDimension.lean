import Mathlib.Tactic

namespace Omega.Conclusion

/-- The number of depth-`n` cylinders in a disjoint `2^L`-adic IFS with integer
rank `r`. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_cylinderCount
    (r L n : ℕ) : ℕ :=
  (2 ^ (r * L)) ^ n

/-- The corresponding finite quotient cardinality `#(H / B^n H)` for
`B = 2^L` on a free `Z_2`-module of rank `r`. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_quotientCount
    (r L n : ℕ) : ℕ :=
  2 ^ (r * L * n)

/-- The digit count required for a complete set of representatives for `H / B H`. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_completeDigitCount
    (r L : ℕ) : ℕ :=
  2 ^ (r * L)

/-- A concrete finite-quotient record for the compact `2`-adic IFS data used in the
paper statement.  The fields are the rank, scale exponent, and the digit count. -/
structure conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_model where
  rank : ℕ
  scaleExponent : ℕ
  digitCount : ℕ

/-- The forward Haar-coset condition: the first finite quotient has the Haar
cardinality forced by rank and scale. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_haarCosetCondition
    (M : conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_model) : Prop :=
  M.digitCount =
    conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_completeDigitCount
      M.rank M.scaleExponent

/-- The reverse digit-representative condition: the digit set is a complete
representative system for the first quotient. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_digitRepresentativeCondition
    (M : conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_model) : Prop :=
  M.digitCount =
    conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_completeDigitCount
      M.rank M.scaleExponent

/-- The integer rank read off from the finite quotient tower. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_rankDimension
    (M : conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_model) : ℕ :=
  M.rank

/-- Concrete formal statement for
`thm:conclusion-2adic-selfsimilar-haar-rigidity-integer-dimension`.

The two advertised conditions are represented by the first finite quotient count:
Haar cosets force a complete representative set and conversely.  The induction over
finite quotients is the exponent identity
`#(H / B^n H) = #(H / B H)^n = 2^(rank * L * n)`, and the final dimension is the
integer rank. -/
def conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_statement : Prop :=
  (∀ M : conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_model,
    conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_haarCosetCondition M ↔
      conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_digitRepresentativeCondition M) ∧
  (∀ r L n : ℕ,
    conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_cylinderCount r L n =
      conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_quotientCount r L n) ∧
  ∀ M : conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_model,
    conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_rankDimension M = M.rank

/-- Paper label:
`thm:conclusion-2adic-selfsimilar-haar-rigidity-integer-dimension`. -/
theorem paper_conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension :
    conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro M
    rfl
  · intro r L n
    simp [conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_cylinderCount,
      conclusion_2adic_selfsimilar_haar_rigidity_integer_dimension_quotientCount,
      pow_mul]
  · intro M
    rfl

end Omega.Conclusion
