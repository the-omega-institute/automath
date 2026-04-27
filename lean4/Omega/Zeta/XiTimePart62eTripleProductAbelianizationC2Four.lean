import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete rank data for the triple-product abelianization.  The three audited factors have
abelianization ranks `1`, `1`, and `2`; the associated elementary `C₂` character group therefore
has rank four. -/
structure xi_time_part62e_triple_product_abelianization_c2_four_data where
  paper_label_xi_time_part62e_triple_product_abelianization_c2_four_firstRank : ℕ
  paper_label_xi_time_part62e_triple_product_abelianization_c2_four_secondRank : ℕ
  paper_label_xi_time_part62e_triple_product_abelianization_c2_four_thirdRank : ℕ
  paper_label_xi_time_part62e_triple_product_abelianization_c2_four_firstRank_eq :
    paper_label_xi_time_part62e_triple_product_abelianization_c2_four_firstRank = 1
  paper_label_xi_time_part62e_triple_product_abelianization_c2_four_secondRank_eq :
    paper_label_xi_time_part62e_triple_product_abelianization_c2_four_secondRank = 1
  paper_label_xi_time_part62e_triple_product_abelianization_c2_four_thirdRank_eq :
    paper_label_xi_time_part62e_triple_product_abelianization_c2_four_thirdRank = 2

namespace xi_time_part62e_triple_product_abelianization_c2_four_data

/-- Sum of the three product-factor abelianization ranks. -/
def abelianizationRank
    (D : xi_time_part62e_triple_product_abelianization_c2_four_data) : ℕ :=
  D.paper_label_xi_time_part62e_triple_product_abelianization_c2_four_firstRank +
    D.paper_label_xi_time_part62e_triple_product_abelianization_c2_four_secondRank +
      D.paper_label_xi_time_part62e_triple_product_abelianization_c2_four_thirdRank

/-- Number of nonzero quadratic characters of the elementary rank-`D.abelianizationRank`
`C₂`-character group. -/
def quadraticSubfieldCount
    (D : xi_time_part62e_triple_product_abelianization_c2_four_data) : ℕ :=
  2 ^ D.abelianizationRank - 1

end xi_time_part62e_triple_product_abelianization_c2_four_data

/-- Paper label: `thm:xi-time-part62e-triple-product-abelianization-c2-four`.  The three
abelianization ranks add as `1 + 1 + 2 = 4`, so the nonzero quadratic characters are
`2^4 - 1 = 15`. -/
theorem paper_xi_time_part62e_triple_product_abelianization_c2_four
    (D : xi_time_part62e_triple_product_abelianization_c2_four_data) :
    D.abelianizationRank = 4 ∧ D.quadraticSubfieldCount = 15 := by
  have hrank : D.abelianizationRank = 4 := by
    simp [xi_time_part62e_triple_product_abelianization_c2_four_data.abelianizationRank,
      D.paper_label_xi_time_part62e_triple_product_abelianization_c2_four_firstRank_eq,
      D.paper_label_xi_time_part62e_triple_product_abelianization_c2_four_secondRank_eq,
      D.paper_label_xi_time_part62e_triple_product_abelianization_c2_four_thirdRank_eq]
  refine ⟨hrank, ?_⟩
  simp [xi_time_part62e_triple_product_abelianization_c2_four_data.quadraticSubfieldCount,
    hrank]

end Omega.Zeta
