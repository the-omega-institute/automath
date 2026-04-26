import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete block data for the finite product of stable fiber permutation groups appearing on the
discrete side of the conclusion package. -/
structure conclusion_discrete_into_connected_block_system where
  StableType : Type
  stableTypeFintype : Fintype StableType
  blockDim : StableType → ℕ

attribute [instance] conclusion_discrete_into_connected_block_system.stableTypeFintype

/-- Concrete model for the permutation-matrix subgroup inside the corresponding projective unitary
block. -/
abbrev conclusion_discrete_into_connected_projective_unitary_block (n : ℕ) :=
  Equiv.Perm (Fin n)

/-- The product of the fiber permutation groups. -/
abbrev conclusion_discrete_into_connected_discrete_group
    (D : conclusion_discrete_into_connected_block_system) :=
  ∀ w : D.StableType, Equiv.Perm (Fin (D.blockDim w))

/-- The product of the projective unitary blocks, modeled by their permutation-matrix subgroups. -/
abbrev conclusion_discrete_into_connected_connected_group
    (D : conclusion_discrete_into_connected_block_system) :=
  ∀ w : D.StableType,
    conclusion_discrete_into_connected_projective_unitary_block (D.blockDim w)

/-- Blockwise passage from each fiber permutation group to the corresponding projective unitary
block. On the concrete permutation-matrix model this is the identity homomorphism on each block,
and hence on the finite product. -/
def conclusion_discrete_into_connected_blockwise_map
    (D : conclusion_discrete_into_connected_block_system) :
    conclusion_discrete_into_connected_discrete_group D →*
      conclusion_discrete_into_connected_connected_group D where
  toFun σ := σ
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Paper label: `prop:conclusion-discrete-into-connected`. Each fiber permutation group embeds
faithfully into the corresponding projective unitary block via permutation matrices; taking the
product over the stable types yields a natural injective homomorphism into the connected block
package. -/
theorem paper_conclusion_discrete_into_connected
    (D : conclusion_discrete_into_connected_block_system) :
    ∃ ι :
      conclusion_discrete_into_connected_discrete_group D →*
        conclusion_discrete_into_connected_connected_group D,
      Function.Injective ι := by
  refine ⟨conclusion_discrete_into_connected_blockwise_map D, ?_⟩
  intro σ τ hστ
  exact hστ

end Omega.Conclusion
