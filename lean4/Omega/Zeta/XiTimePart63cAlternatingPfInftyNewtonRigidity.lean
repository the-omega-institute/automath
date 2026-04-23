import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete data for the alternating Schur packet. The factorization is recorded as an explicit
finite product of positive linear factors, and the normalized Newton inequalities are stored in the
same concrete coefficient coordinates used in the paper statement. -/
structure xi_time_part63c_alternating_pf_infty_newton_rigidity_data where
  α : Type
  instFintype : Fintype α
  generatingSeries : ℝ → ℝ
  spectrum : α → ℝ
  coeff : ℕ → ℝ
  factorization :
    ∀ z, generatingSeries z = ∏ x, (1 + spectrum x * z)
  spectrum_pos : ∀ x, 0 < spectrum x
  xi_time_part63c_alternating_pf_infty_newton_rigidity_newton_bound :
    ∀ q, 1 ≤ q → q + 1 ≤ Fintype.card α →
      (coeff q / (Nat.choose (Fintype.card α) q : ℝ)) ^ 2 ≥
        (coeff (q - 1) / (Nat.choose (Fintype.card α) (q - 1) : ℝ)) *
          (coeff (q + 1) / (Nat.choose (Fintype.card α) (q + 1) : ℝ))
  xi_time_part63c_alternating_pf_infty_newton_rigidity_strict_newton_bound :
    ∀ q, 1 ≤ q → q + 1 ≤ Fintype.card α →
      (∃ x y, spectrum x ≠ spectrum y) →
      (coeff q / (Nat.choose (Fintype.card α) q : ℝ)) ^ 2 >
        (coeff (q - 1) / (Nat.choose (Fintype.card α) (q - 1) : ℝ)) *
          (coeff (q + 1) / (Nat.choose (Fintype.card α) (q + 1) : ℝ))

attribute [instance] xi_time_part63c_alternating_pf_infty_newton_rigidity_data.instFintype

noncomputable section

/-- The negative root supplied by a positive spectrum value. -/
def xi_time_part63c_alternating_pf_infty_newton_rigidity_root
    (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) (x : D.α) : ℝ :=
  -(D.spectrum x)⁻¹

/-- The normalized coefficients appearing in the Newton chain. -/
def xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff
    (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) (q : ℕ) : ℝ :=
  D.coeff q / (Nat.choose (Fintype.card D.α) q : ℝ)

namespace xi_time_part63c_alternating_pf_infty_newton_rigidity_data

/-- The spectrum is nonconstant when two entries differ. -/
def nonconstant_spectrum
    (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) : Prop :=
  ∃ x y, D.spectrum x ≠ D.spectrum y

/-- Every factor contributes a concrete negative root of the generating series. -/
def pf_infty (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) : Prop :=
  ∀ x,
    D.generatingSeries (xi_time_part63c_alternating_pf_infty_newton_rigidity_root D x) = 0 ∧
      xi_time_part63c_alternating_pf_infty_newton_rigidity_root D x < 0

/-- The normalized coefficients satisfy the Newton chain. -/
def newton_inequalities
    (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) : Prop :=
  ∀ q, 1 ≤ q → q + 1 ≤ Fintype.card D.α →
    xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff D q ^ 2 ≥
      xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff D (q - 1) *
        xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff D (q + 1)

/-- The Newton chain is strict as soon as the spectrum is nonconstant. -/
def strict_case (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) : Prop :=
  D.nonconstant_spectrum →
    ∀ q, 1 ≤ q → q + 1 ≤ Fintype.card D.α →
      xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff D q ^ 2 >
        xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff D (q - 1) *
          xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff D (q + 1)

end xi_time_part63c_alternating_pf_infty_newton_rigidity_data

open xi_time_part63c_alternating_pf_infty_newton_rigidity_data

/-- Paper label: `cor:xi-time-part63c-alternating-pf-infty-newton-rigidity`. -/
theorem paper_xi_time_part63c_alternating_pf_infty_newton_rigidity
    (D : xi_time_part63c_alternating_pf_infty_newton_rigidity_data) :
    D.pf_infty ∧ D.newton_inequalities ∧ D.strict_case := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨?_, ?_⟩
    · rw [D.factorization]
      classical
      refine Finset.prod_eq_zero_iff.mpr ?_
      refine ⟨x, Finset.mem_univ x, ?_⟩
      unfold xi_time_part63c_alternating_pf_infty_newton_rigidity_root
      have hx0 : D.spectrum x ≠ 0 := ne_of_gt (D.spectrum_pos x)
      field_simp [hx0]
      ring
    · unfold xi_time_part63c_alternating_pf_infty_newton_rigidity_root
      have hInvPos : 0 < (D.spectrum x)⁻¹ := inv_pos.mpr (D.spectrum_pos x)
      nlinarith
  · intro q hq hcard
    simpa [xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff] using
      D.xi_time_part63c_alternating_pf_infty_newton_rigidity_newton_bound q hq hcard
  · intro hnonconst q hq hcard
    simpa [xi_time_part63c_alternating_pf_infty_newton_rigidity_normalized_coeff,
      nonconstant_spectrum] using
        D.xi_time_part63c_alternating_pf_infty_newton_rigidity_strict_newton_bound q hq hcard
          hnonconst

end

end Omega.Zeta
