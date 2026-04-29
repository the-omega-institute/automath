import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets

namespace Omega.Conclusion

open scoped Classical

/-- Concrete finite coding data for the coarse-graining Gödel bit-tax bound. -/
structure conclusion_cyclelattice_coarsegraining_godel_bit_tax_data where
  conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice : Finset ℕ
  conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient : Finset ℕ
  conclusion_cyclelattice_coarsegraining_godel_bit_tax_bit_budget : ℕ
  conclusion_cyclelattice_coarsegraining_godel_bit_tax_encode :
    {x // x ∈ conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice} ↪
      {q // q ∈ conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient} ×
        (Fin conclusion_cyclelattice_coarsegraining_godel_bit_tax_bit_budget → Bool)

namespace conclusion_cyclelattice_coarsegraining_godel_bit_tax_data

/-- The finite cardinal bit-tax inequality forced by an injective coarse-grained code. -/
def conclusion_cyclelattice_coarsegraining_godel_bit_tax_statement
    (D : conclusion_cyclelattice_coarsegraining_godel_bit_tax_data) : Prop :=
  D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice.card ≤
    D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient.card *
      2 ^ D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_bit_budget

end conclusion_cyclelattice_coarsegraining_godel_bit_tax_data

/-- Paper label: `cor:conclusion-cyclelattice-coarsegraining-godel-bit-tax`. -/
theorem paper_conclusion_cyclelattice_coarsegraining_godel_bit_tax
    (D : conclusion_cyclelattice_coarsegraining_godel_bit_tax_data) :
    D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_statement := by
  classical
  letI : Fintype
      {x // x ∈ D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice} :=
    Finset.Subtype.fintype D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice
  letI : Fintype
      {q // q ∈ D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient} :=
    Finset.Subtype.fintype D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient
  unfold
    conclusion_cyclelattice_coarsegraining_godel_bit_tax_data.conclusion_cyclelattice_coarsegraining_godel_bit_tax_statement
  calc
    D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice.card =
        Fintype.card
          {x // x ∈ D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_lattice} := by
      simp
    _ ≤
        Fintype.card
          ({q // q ∈ D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient} ×
            (Fin D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_bit_budget → Bool)) := by
      exact Fintype.card_le_of_embedding
        D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_encode
    _ = D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_quotient.card *
          2 ^ D.conclusion_cyclelattice_coarsegraining_godel_bit_tax_bit_budget := by
      rw [Fintype.card_prod, Fintype.card_pi_const, Fintype.card_bool]
      simp

end Omega.Conclusion
