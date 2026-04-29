import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The Curie--Weiss zero-field weight `A = Σ h^(2k)`. -/
def xi_hdqcd_cw_tricritical_A (N : ℕ) (h : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun k => h ^ (2 * k)

/-- The Curie--Weiss zero-field weight `B = h^N`. -/
def xi_hdqcd_cw_tricritical_B (N : ℕ) (h : ℝ) : ℝ :=
  h ^ N

/-- The spinodal obtained from the vanishing of the quadratic coefficient at the origin. -/
def xi_hdqcd_cw_tricritical_spinodal (A B : ℝ) : ℝ :=
  (A + 2 * B) / (2 * B)

/-- The quartic Landau coefficient evaluated at the spinodal. -/
def xi_hdqcd_cw_tricritical_quarticCoefficient (A B : ℝ) : ℝ :=
  ((A + 2 * B) ^ 2 * (4 * B - A)) / (192 * B ^ 3)

/-- The tricritical relation normalized by dividing through by `B = h^N`. -/
def xi_hdqcd_cw_tricritical_normalizedEquation (N : ℕ) (h : ℝ) : ℝ :=
  xi_hdqcd_cw_tricritical_A N h / xi_hdqcd_cw_tricritical_B N h

lemma xi_hdqcd_cw_tricritical_balance_iff_normalized (N : ℕ) (h : ℝ) (hh : h ≠ 0) :
    xi_hdqcd_cw_tricritical_A N h = 4 * xi_hdqcd_cw_tricritical_B N h ↔
      xi_hdqcd_cw_tricritical_normalizedEquation N h = 4 := by
  have hB0 : xi_hdqcd_cw_tricritical_B N h ≠ 0 := by
    unfold xi_hdqcd_cw_tricritical_B
    exact pow_ne_zero N hh
  constructor
  · intro hEq
    unfold xi_hdqcd_cw_tricritical_normalizedEquation
    rw [hEq]
    field_simp [hB0]
  · intro hEq
    unfold xi_hdqcd_cw_tricritical_normalizedEquation at hEq
    exact (div_eq_iff hB0).mp hEq

/-- Paper label: `thm:xi-hdqcd-cw-tricritical`.

This Lean wrapper records the algebraic core of the Curie--Weiss tricritical analysis: the
spinodal and quartic coefficients have their closed forms, the induced tricritical condition
`A = 4B` is equivalent to the normalized equation `A / B = 4` whenever `h ≠ 0`, and the explicit
`N = 3`, `h = 1` specialization gives the tricritical point `J = 3` with vanishing quartic
coefficient. -/
theorem paper_xi_hdqcd_cw_tricritical :
    (∀ A B : ℝ, 0 < B →
      xi_hdqcd_cw_tricritical_spinodal A B = (A + 2 * B) / (2 * B) ∧
        xi_hdqcd_cw_tricritical_quarticCoefficient A B =
          ((A + 2 * B) ^ 2 * (4 * B - A)) / (192 * B ^ 3)) ∧
    (∀ N : ℕ, ∀ h : ℝ, h ≠ 0 →
      (xi_hdqcd_cw_tricritical_A N h = 4 * xi_hdqcd_cw_tricritical_B N h ↔
        xi_hdqcd_cw_tricritical_normalizedEquation N h = 4)) ∧
    xi_hdqcd_cw_tricritical_normalizedEquation 3 1 = 4 ∧
    xi_hdqcd_cw_tricritical_spinodal
        (xi_hdqcd_cw_tricritical_A 3 1) (xi_hdqcd_cw_tricritical_B 3 1) = 3 ∧
    xi_hdqcd_cw_tricritical_quarticCoefficient
        (xi_hdqcd_cw_tricritical_A 3 1) (xi_hdqcd_cw_tricritical_B 3 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B _hB
    exact ⟨rfl, rfl⟩
  · intro N h hh
    exact xi_hdqcd_cw_tricritical_balance_iff_normalized N h hh
  · norm_num [xi_hdqcd_cw_tricritical_normalizedEquation, xi_hdqcd_cw_tricritical_A,
      xi_hdqcd_cw_tricritical_B]
  · norm_num [xi_hdqcd_cw_tricritical_spinodal, xi_hdqcd_cw_tricritical_A,
      xi_hdqcd_cw_tricritical_B]
  · norm_num [xi_hdqcd_cw_tricritical_quarticCoefficient, xi_hdqcd_cw_tricritical_A,
      xi_hdqcd_cw_tricritical_B]

end

end Omega.Zeta
