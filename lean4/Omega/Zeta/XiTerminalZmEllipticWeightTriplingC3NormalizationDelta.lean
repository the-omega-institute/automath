import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete bidegree and normalization package for the weight-tripling curve `C_3`.
The curve has bidegree `(36, 4)` on `P^1 x P^1`; its normalization has genus `1`,
and the total delta invariant is the arithmetic genus minus the normalization genus. -/
structure xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data where
  bidegreeY : ℕ
  bidegreeY3 : ℕ
  normalizationGenus : ℕ
  arithmeticGenus : ℕ
  deltaSum : ℕ
  bidegreeY_eq : bidegreeY = 36
  bidegreeY3_eq : bidegreeY3 = 4
  arithmeticGenus_eq_bidegree : arithmeticGenus = (bidegreeY - 1) * (bidegreeY3 - 1)
  normalizationGenus_eq_one : normalizationGenus = 1
  deltaSum_eq_genus_drop : deltaSum = arithmeticGenus - normalizationGenus

namespace xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data

/-- The normalization is elliptic, recorded by genus one. -/
def normalizationIsElliptic
    (D : xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data) : Prop :=
  D.normalizationGenus = 1

lemma arithmeticGenus_eq_105
    (D : xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data) :
    D.arithmeticGenus = 105 := by
  calc
    D.arithmeticGenus = (D.bidegreeY - 1) * (D.bidegreeY3 - 1) :=
      D.arithmeticGenus_eq_bidegree
    _ = (36 - 1) * (4 - 1) := by rw [D.bidegreeY_eq, D.bidegreeY3_eq]
    _ = 105 := by norm_num

lemma deltaSum_eq_104
    (D : xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data) :
    D.deltaSum = 104 := by
  calc
    D.deltaSum = D.arithmeticGenus - D.normalizationGenus := D.deltaSum_eq_genus_drop
    _ = 105 - 1 := by rw [D.arithmeticGenus_eq_105, D.normalizationGenus_eq_one]
    _ = 104 := by norm_num

end xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data

open xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data

/-- Paper label:
`thm:xi-terminal-zm-elliptic-weight-tripling-c3-normalization-delta`. -/
theorem paper_xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta
    (D : xi_terminal_zm_elliptic_weight_tripling_c3_normalization_delta_data) :
    D.normalizationIsElliptic ∧ D.arithmeticGenus = 105 ∧ D.deltaSum = 104 := by
  exact ⟨D.normalizationGenus_eq_one, D.arithmeticGenus_eq_105, D.deltaSum_eq_104⟩

end Omega.Zeta
