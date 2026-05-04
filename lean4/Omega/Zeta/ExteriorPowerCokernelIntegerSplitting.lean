import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete exterior-power cokernel splitting package.
The Smith-Schubert decomposition gives the cokernel as a finite direct product of cyclic summand
models, and the integer splitting certificate identifies that product with the displayed integer
splitting object. -/
structure xi_exterior_power_cokernel_integer_splitting_data where
  Cokernel : Type*
  IntegerSplitting : Type*
  SmithIndex : Type*
  SmithSummand : SmithIndex → Type*
  xi_exterior_power_cokernel_integer_splitting_smith_schubert_decomposition :
    Cokernel ≃ (∀ i : SmithIndex, SmithSummand i)
  xi_exterior_power_cokernel_integer_splitting_integer_summand_assembly :
    (∀ i : SmithIndex, SmithSummand i) ≃ IntegerSplitting

/-- Paper label: `cor:xi-exterior-power-cokernel-integer-splitting`. -/
theorem paper_xi_exterior_power_cokernel_integer_splitting
    (D : xi_exterior_power_cokernel_integer_splitting_data) :
    ∃ e : D.Cokernel → D.IntegerSplitting, Function.Bijective e := by
  let e : D.Cokernel ≃ D.IntegerSplitting :=
    D.xi_exterior_power_cokernel_integer_splitting_smith_schubert_decomposition.trans
      D.xi_exterior_power_cokernel_integer_splitting_integer_summand_assembly
  exact ⟨e, e.bijective⟩

end Omega.Zeta
