import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.XiJSexticEllipticLattesTMap

namespace Omega.Zeta

noncomputable section

/-- Concrete input for the normalized Belyi package. -/
structure xi_j_sextic_elliptic_lattes_belyi_normalization_data where
  t : ℝ
  ht : t ≠ 1728
  hQ : t ^ 2 + 1862 * t + 161792 ≠ 0

/-- The branch value `α = -931 - 89 √89`. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_alpha : ℝ :=
  -931 - 89 * Real.sqrt 89

/-- The branch value `β = -931 + 89 √89`. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_beta : ℝ :=
  -931 + 89 * Real.sqrt 89

/-- The explicit Möbius numerator sending `α` to `0`. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusNumerator (z : ℝ) : ℝ :=
  (1728 - xi_j_sextic_elliptic_lattes_belyi_normalization_beta) *
    (z - xi_j_sextic_elliptic_lattes_belyi_normalization_alpha)

/-- The explicit Möbius denominator sending `β` to `∞`. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusDenominator (z : ℝ) : ℝ :=
  (1728 - xi_j_sextic_elliptic_lattes_belyi_normalization_alpha) *
    (z - xi_j_sextic_elliptic_lattes_belyi_normalization_beta)

/-- The normalized Belyi map `ψ(z)`. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_mobius (z : ℝ) : ℝ :=
  xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusNumerator z /
    xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusDenominator z

/-- Transport of the three-branch square factorization to the normalized Belyi setting. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_branchTransport
    (D : xi_j_sextic_elliptic_lattes_belyi_normalization_data) : Prop :=
  let α : ℝ := xi_j_sextic_elliptic_lattes_belyi_normalization_alpha
  let β : ℝ := xi_j_sextic_elliptic_lattes_belyi_normalization_beta
  let Q : ℝ := D.t ^ 2 + 1862 * D.t + 161792
  let L : ℝ :=
    (D.t ^ 4 + 6111488 * D.t ^ 2 + 2236612608 * D.t + 9487424438272) /
      (4 * (D.t - 1728) * Q)
  L - 1728 = (D.t ^ 2 - 3456 * D.t - 3379328) ^ 2 / (4 * (D.t - 1728) * Q) ∧
    L - α =
      (D.t ^ 2 + (1862 + 178 * Real.sqrt 89) * D.t + 161792 - 307584 * Real.sqrt 89) ^ 2 /
        (4 * (D.t - 1728) * Q) ∧
    L - β =
      (D.t ^ 2 + (1862 - 178 * Real.sqrt 89) * D.t + 161792 + 307584 * Real.sqrt 89) ^ 2 /
        (4 * (D.t - 1728) * Q)

/-- The normalized passport `(2^2, 2^2, 2^2)`. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_passport : List (List ℕ) :=
  [[2, 2], [2, 2], [2, 2]]

/-- A concrete four-element witness for the deck group `(ℤ / 2ℤ)^2`. -/
abbrev xi_j_sextic_elliptic_lattes_belyi_normalization_deckGroup := Fin 2 × Fin 2

/-- Paper-facing normalization package. -/
def xi_j_sextic_elliptic_lattes_belyi_normalization_statement
    (D : xi_j_sextic_elliptic_lattes_belyi_normalization_data) : Prop :=
  xi_j_sextic_elliptic_lattes_belyi_normalization_branchTransport D ∧
    xi_j_sextic_elliptic_lattes_belyi_normalization_mobius
        xi_j_sextic_elliptic_lattes_belyi_normalization_alpha = 0 ∧
    xi_j_sextic_elliptic_lattes_belyi_normalization_mobius 1728 = 1 ∧
    xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusDenominator
        xi_j_sextic_elliptic_lattes_belyi_normalization_beta = 0 ∧
    xi_j_sextic_elliptic_lattes_belyi_normalization_passport = [[2, 2], [2, 2], [2, 2]] ∧
    Fintype.card xi_j_sextic_elliptic_lattes_belyi_normalization_deckGroup = 4

theorem xi_j_sextic_elliptic_lattes_belyi_normalization_alpha_ne_beta :
    xi_j_sextic_elliptic_lattes_belyi_normalization_alpha ≠
      xi_j_sextic_elliptic_lattes_belyi_normalization_beta := by
  have hsqrt89_pos : 0 < Real.sqrt 89 := by
    exact Real.sqrt_pos.2 (by norm_num)
  unfold xi_j_sextic_elliptic_lattes_belyi_normalization_alpha
    xi_j_sextic_elliptic_lattes_belyi_normalization_beta
  linarith

theorem xi_j_sextic_elliptic_lattes_belyi_normalization_alpha_ne_1728 :
    xi_j_sextic_elliptic_lattes_belyi_normalization_alpha ≠ 1728 := by
  have hsqrt89_pos : 0 < Real.sqrt 89 := by
    exact Real.sqrt_pos.2 (by norm_num)
  unfold xi_j_sextic_elliptic_lattes_belyi_normalization_alpha
  linarith

theorem xi_j_sextic_elliptic_lattes_belyi_normalization_beta_ne_1728 :
    xi_j_sextic_elliptic_lattes_belyi_normalization_beta ≠ 1728 := by
  have hsqrt89_lt_ten : Real.sqrt 89 < 10 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (89 : ℝ) by positivity)]
  unfold xi_j_sextic_elliptic_lattes_belyi_normalization_beta
  linarith

/-- Paper label: `thm:xi-j-sextic-elliptic-lattes-belyi-normalization`. -/
theorem paper_xi_j_sextic_elliptic_lattes_belyi_normalization
    (D : xi_j_sextic_elliptic_lattes_belyi_normalization_data) :
    xi_j_sextic_elliptic_lattes_belyi_normalization_statement D := by
  have hbranch :=
    paper_xi_j_sextic_elliptic_lattes_three_branch_square_factorization D.t D.ht D.hQ
  have halpha_beta :
      xi_j_sextic_elliptic_lattes_belyi_normalization_alpha ≠
        xi_j_sextic_elliptic_lattes_belyi_normalization_beta :=
    xi_j_sextic_elliptic_lattes_belyi_normalization_alpha_ne_beta
  have halpha_1728 :
      xi_j_sextic_elliptic_lattes_belyi_normalization_alpha ≠ 1728 :=
    xi_j_sextic_elliptic_lattes_belyi_normalization_alpha_ne_1728
  have hbeta_1728 :
      xi_j_sextic_elliptic_lattes_belyi_normalization_beta ≠ 1728 :=
    xi_j_sextic_elliptic_lattes_belyi_normalization_beta_ne_1728
  refine ⟨hbranch, ?_, ?_, ?_, rfl, ?_⟩
  · unfold xi_j_sextic_elliptic_lattes_belyi_normalization_mobius
      xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusNumerator
      xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusDenominator
    field_simp [halpha_beta, sub_ne_zero.mpr halpha_1728]
    ring_nf
  · unfold xi_j_sextic_elliptic_lattes_belyi_normalization_mobius
      xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusNumerator
      xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusDenominator
    have hden :
        (1728 - xi_j_sextic_elliptic_lattes_belyi_normalization_alpha) *
            (1728 - xi_j_sextic_elliptic_lattes_belyi_normalization_beta) ≠
          0 := by
      exact mul_ne_zero (sub_ne_zero.mpr halpha_1728.symm) (sub_ne_zero.mpr hbeta_1728.symm)
    rw [mul_comm
        (1728 - xi_j_sextic_elliptic_lattes_belyi_normalization_beta)
        (1728 - xi_j_sextic_elliptic_lattes_belyi_normalization_alpha)]
    exact div_self hden
  · unfold xi_j_sextic_elliptic_lattes_belyi_normalization_mobiusDenominator
      xi_j_sextic_elliptic_lattes_belyi_normalization_beta
    ring
  · native_decide

end

end Omega.Zeta
