import Omega.OperatorAlgebra.FoldWreathAbelianizationCharacters

open scoped BigOperators

theorem paper_conclusion_fold_normalizer_abelianization_layered_characters
    (layers : Finset (Nat × Nat)) (hpos : ∀ dn ∈ layers, 1 <= dn.1) :
    Finset.prod layers (fun dn => Omega.OperatorAlgebra.foldWreathAbelianizationOrder dn.1 dn.2) =
      2 ^ Finset.sum layers
        (fun dn => (Omega.OperatorAlgebra.foldWreathCharacterBasis dn.1 dn.2).card) := by
  classical
  revert hpos
  refine Finset.induction_on layers ?empty ?insert
  · intro hpos
    simp
  · intro dn layers hdn ih hpos_insert
    have hpos_layers : ∀ e ∈ layers, 1 <= e.1 := by
      intro e he
      exact hpos_insert e (by simp [he])
    have hdn_pos : 1 <= dn.1 := hpos_insert dn (by simp)
    have hlocal :
        Omega.OperatorAlgebra.foldWreathAbelianizationOrder dn.1 dn.2 =
          2 ^ (Omega.OperatorAlgebra.foldWreathCharacterBasis dn.1 dn.2).card :=
      (Omega.OperatorAlgebra.paper_op_algebra_fold_wreath_abelianization_characters
        dn.1 dn.2 hdn_pos).2.2
    rw [Finset.prod_insert hdn, Finset.sum_insert hdn, hlocal, ih hpos_layers, ← Nat.pow_add]
