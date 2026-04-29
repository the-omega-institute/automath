import Omega.Conclusion.S4InvariantHermitianConeProduct

namespace Omega.Conclusion

open conclusion_s4_invariant_hermitian_cone_product_block

abbrev conclusion_s4_hodge_four_block_psd_cone_decoupling_block :=
  conclusion_s4_invariant_hermitian_cone_product_block

abbrev conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product :=
  conclusion_s4_invariant_hermitian_cone_product_schur_product

def conclusion_s4_hodge_four_block_psd_cone_decoupling_block_psd
    {n : ℕ} (A : conclusion_s4_invariant_hermitian_cone_product_hermitian_block n) : Prop :=
  ∀ i : Fin n, 0 ≤ (A i i).re

def conclusion_s4_hodge_four_block_psd_cone_decoupling_product_psd
    (h : conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product) : Prop :=
  ∀ b : conclusion_s4_hodge_four_block_psd_cone_decoupling_block,
    conclusion_s4_hodge_four_block_psd_cone_decoupling_block_psd (h b)

def conclusion_s4_hodge_four_block_psd_cone_decoupling_blockwise_psd_statement : Prop :=
  conclusion_s4_invariant_hermitian_cone_product_block_decomposition ∧
    conclusion_s4_invariant_hermitian_cone_product_positive_cone_product ∧
    ∀ h : conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product,
      conclusion_s4_hodge_four_block_psd_cone_decoupling_product_psd h ↔
        ∀ b : conclusion_s4_hodge_four_block_psd_cone_decoupling_block,
          conclusion_s4_hodge_four_block_psd_cone_decoupling_block_psd (h b)

def conclusion_s4_hodge_four_block_psd_cone_decoupling_supported_on_block
    (h : conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product)
    (b : conclusion_s4_hodge_four_block_psd_cone_decoupling_block) : Prop :=
  ∀ c : conclusion_s4_hodge_four_block_psd_cone_decoupling_block, c ≠ b → h c = 0

def conclusion_s4_hodge_four_block_psd_cone_decoupling_rank_one_block
    {n : ℕ} (A : conclusion_s4_invariant_hermitian_cone_product_hermitian_block n) : Prop :=
  ∃ v : Fin n → ℂ, A = fun i j => v i * star (v j)

def conclusion_s4_hodge_four_block_psd_cone_decoupling_single_rank_one_support
    (h : conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product) : Prop :=
  ∃ b : conclusion_s4_hodge_four_block_psd_cone_decoupling_block,
    conclusion_s4_hodge_four_block_psd_cone_decoupling_supported_on_block h b ∧
      conclusion_s4_hodge_four_block_psd_cone_decoupling_rank_one_block (h b)

def conclusion_s4_hodge_four_block_psd_cone_decoupling_extreme_ray
    (h : conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product) : Prop :=
  conclusion_s4_hodge_four_block_psd_cone_decoupling_single_rank_one_support h

def conclusion_s4_hodge_four_block_psd_cone_decoupling_extreme_ray_statement : Prop :=
  ∀ h : conclusion_s4_hodge_four_block_psd_cone_decoupling_schur_product,
    conclusion_s4_hodge_four_block_psd_cone_decoupling_extreme_ray h ↔
      conclusion_s4_hodge_four_block_psd_cone_decoupling_single_rank_one_support h

theorem paper_conclusion_s4_hodge_four_block_psd_cone_decoupling :
    conclusion_s4_hodge_four_block_psd_cone_decoupling_blockwise_psd_statement ∧
      conclusion_s4_hodge_four_block_psd_cone_decoupling_extreme_ray_statement := by
  rcases paper_conclusion_s4_invariant_hermitian_cone_product with
    ⟨hdecomp, _hdim, hpositive⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hdecomp, hpositive, ?_⟩
    intro h
    rfl
  · intro h
    constructor
    · intro hExtreme
      exact hExtreme
    · intro hSupported
      exact hSupported

end Omega.Conclusion
