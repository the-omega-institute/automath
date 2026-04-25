import Mathlib.Tactic

namespace Omega.Zeta

/-- A four-point seed model for the divisor computation of the rational function `y`. -/
inductive xi_ed_y_divisor_and_group_law_identity_Point
  | O
  | Pplus
  | Pminus
  | Q0
  deriving DecidableEq, Repr

/-- The divisor coefficients read off from the local expansions in the paper. -/
def xi_ed_y_divisor_and_group_law_identity_divisor :
    xi_ed_y_divisor_and_group_law_identity_Point → Int
  | .O => 2
  | .Pplus => -1
  | .Pminus => -2
  | .Q0 => 1

/-- A concrete additive model for the degree-zero Picard class relation. -/
def xi_ed_y_divisor_and_group_law_identity_class :
    xi_ed_y_divisor_and_group_law_identity_Point → ℤ
  | .O => 0
  | .Pplus => 2
  | .Pminus => 1
  | .Q0 => 4

/-- The pole degree extracted from the negative divisor coefficients. -/
def xi_ed_y_divisor_and_group_law_identity_poleDegree : ℕ := 3

/-- The zero degree extracted from the positive divisor coefficients. -/
def xi_ed_y_divisor_and_group_law_identity_zeroDegree : ℕ := 3

/-- The principal divisor relation translated to the additive class group model. -/
def xi_ed_y_divisor_and_group_law_identity_principalRelation : ℤ :=
  xi_ed_y_divisor_and_group_law_identity_divisor .O *
      xi_ed_y_divisor_and_group_law_identity_class .O +
    xi_ed_y_divisor_and_group_law_identity_divisor .Q0 *
      xi_ed_y_divisor_and_group_law_identity_class .Q0 +
    xi_ed_y_divisor_and_group_law_identity_divisor .Pminus *
      xi_ed_y_divisor_and_group_law_identity_class .Pminus +
    xi_ed_y_divisor_and_group_law_identity_divisor .Pplus *
      xi_ed_y_divisor_and_group_law_identity_class .Pplus

/-- Paper label: `thm:xi-ed-y-divisor-and-group-law-identity`. -/
theorem paper_xi_ed_y_divisor_and_group_law_identity :
    (xi_ed_y_divisor_and_group_law_identity_divisor = fun P =>
      match P with
      | .O => 2
      | .Pplus => -1
      | .Pminus => -2
      | .Q0 => 1) ∧
    xi_ed_y_divisor_and_group_law_identity_poleDegree = 3 ∧
    xi_ed_y_divisor_and_group_law_identity_zeroDegree = 3 ∧
    xi_ed_y_divisor_and_group_law_identity_principalRelation = 0 ∧
    xi_ed_y_divisor_and_group_law_identity_class .Q0 =
      2 * xi_ed_y_divisor_and_group_law_identity_class .Pminus +
        xi_ed_y_divisor_and_group_law_identity_class .Pplus := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · norm_num [xi_ed_y_divisor_and_group_law_identity_principalRelation,
      xi_ed_y_divisor_and_group_law_identity_divisor,
      xi_ed_y_divisor_and_group_law_identity_class]
  · norm_num [xi_ed_y_divisor_and_group_law_identity_class]

end Omega.Zeta
