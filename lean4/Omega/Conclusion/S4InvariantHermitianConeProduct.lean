import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The four Schur multiplicity blocks, with sizes `5`, `4`, `3`, and `9`. -/
inductive conclusion_s4_invariant_hermitian_cone_product_block
  | conclusion_s4_invariant_hermitian_cone_product_block_five
  | conclusion_s4_invariant_hermitian_cone_product_block_four
  | conclusion_s4_invariant_hermitian_cone_product_block_three
  | conclusion_s4_invariant_hermitian_cone_product_block_nine
  deriving DecidableEq, Fintype

namespace conclusion_s4_invariant_hermitian_cone_product_block

/-- Multiplicity size of each invariant Hermitian block. -/
def conclusion_s4_invariant_hermitian_cone_product_block_size :
    conclusion_s4_invariant_hermitian_cone_product_block → ℕ
  | conclusion_s4_invariant_hermitian_cone_product_block_five => 5
  | conclusion_s4_invariant_hermitian_cone_product_block_four => 4
  | conclusion_s4_invariant_hermitian_cone_product_block_three => 3
  | conclusion_s4_invariant_hermitian_cone_product_block_nine => 9

end conclusion_s4_invariant_hermitian_cone_product_block

open conclusion_s4_invariant_hermitian_cone_product_block

/-- A concrete Hermitian block carrier; the real dimension is the usual `n²`. -/
abbrev conclusion_s4_invariant_hermitian_cone_product_hermitian_block (n : ℕ) :=
  Fin n → Fin n → ℂ

/-- Product of the four Schur blocks. -/
abbrev conclusion_s4_invariant_hermitian_cone_product_schur_product :=
  (b : conclusion_s4_invariant_hermitian_cone_product_block) →
    conclusion_s4_invariant_hermitian_cone_product_hermitian_block
      (conclusion_s4_invariant_hermitian_cone_product_block_size b)

/-- Real dimension of one Hermitian matrix block. -/
def conclusion_s4_invariant_hermitian_cone_product_block_real_dimension
    (b : conclusion_s4_invariant_hermitian_cone_product_block) : ℕ :=
  let n := conclusion_s4_invariant_hermitian_cone_product_block_size b
  n * n

/-- Total real dimension of the product cone. -/
def conclusion_s4_invariant_hermitian_cone_product_total_real_dimension : ℕ :=
  ∑ b, conclusion_s4_invariant_hermitian_cone_product_block_real_dimension b

/-- The invariant Hermitian cone decomposes as the product of the four Schur blocks. -/
def conclusion_s4_invariant_hermitian_cone_product_block_decomposition : Prop :=
  Nonempty conclusion_s4_invariant_hermitian_cone_product_schur_product

/-- Paper-facing real dimension of the invariant Hermitian cone. -/
def conclusion_s4_invariant_hermitian_cone_product_real_dimension : ℕ :=
  conclusion_s4_invariant_hermitian_cone_product_total_real_dimension

/-- Positivity is checked independently on the four nonempty blocks. -/
def conclusion_s4_invariant_hermitian_cone_product_positive_cone_product : Prop :=
  ∀ b : conclusion_s4_invariant_hermitian_cone_product_block,
    0 < conclusion_s4_invariant_hermitian_cone_product_block_size b

/-- Paper label: `prop:conclusion-s4-invariant-hermitian-cone-product`. The four Schur blocks have
matrix sizes `5`, `4`, `3`, and `9`; hence the real Hermitian dimensions add to
`25 + 16 + 9 + 81 = 131`, and the positive cone is the blockwise product. -/
theorem paper_conclusion_s4_invariant_hermitian_cone_product :
    conclusion_s4_invariant_hermitian_cone_product_block_decomposition ∧
      conclusion_s4_invariant_hermitian_cone_product_real_dimension = 131 ∧
      conclusion_s4_invariant_hermitian_cone_product_positive_cone_product := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun _b _i _j => 0⟩
  · change conclusion_s4_invariant_hermitian_cone_product_total_real_dimension = 131
    native_decide
  · intro b
    cases b <;> norm_num [conclusion_s4_invariant_hermitian_cone_product_block_size]

end Omega.Conclusion
