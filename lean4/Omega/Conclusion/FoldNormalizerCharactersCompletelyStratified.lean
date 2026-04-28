import Omega.Conclusion.FoldNormalizerAbelianizationLayeredCharacters

open scoped BigOperators

/-- Paper label: `thm:conclusion-fold-normalizer-characters-completely-stratified`. -/
theorem paper_conclusion_fold_normalizer_characters_completely_stratified
    (layers : Finset (Nat × Nat)) (hpos : ∀ dn ∈ layers, 1 <= dn.1) :
    ∃ alpha : Nat,
      alpha =
          Finset.sum layers
            (fun dn => (Omega.OperatorAlgebra.foldWreathCharacterBasis dn.1 dn.2).card) ∧
        Finset.prod layers
            (fun dn => Omega.OperatorAlgebra.foldWreathAbelianizationOrder dn.1 dn.2) =
          2 ^ alpha := by
  refine ⟨Finset.sum layers
      (fun dn => (Omega.OperatorAlgebra.foldWreathCharacterBasis dn.1 dn.2).card), rfl, ?_⟩
  simpa using paper_conclusion_fold_normalizer_abelianization_layered_characters layers hpos
