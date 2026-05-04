import Mathlib.Tactic

namespace Omega.Zeta

/-- The even Taylor coefficient of `sinh (sqrt z * scale / 2) / (sqrt z * scale / 2)`.
The paper theorem uses `scale = 1` and `scale = phi`. -/
def xi_time_part9zbj_lp_pf_rigidity_sinh_coeff (scale : ℚ) (n : ℕ) : ℚ :=
  scale ^ (2 * n) / ((4 : ℚ) ^ n * (Nat.factorial (2 * n + 1) : ℚ))

/-- The finite Cauchy-product coefficient of the two normalized sinh series. -/
def xi_time_part9zbj_lp_pf_rigidity_product_coeff (phi : ℚ) (m : ℕ) : ℚ :=
  Finset.sum (Finset.range (m + 1)) fun j =>
    xi_time_part9zbj_lp_pf_rigidity_sinh_coeff 1 (m - j) *
      xi_time_part9zbj_lp_pf_rigidity_sinh_coeff phi j

/-- The coefficient formula obtained after collecting the common `4 ^ m` factor. -/
def xi_time_part9zbj_lp_pf_rigidity_explicit_coeff (phi : ℚ) (m : ℕ) : ℚ :=
  (1 / (4 : ℚ) ^ m) *
    Finset.sum (Finset.range (m + 1)) fun j =>
      phi ^ (2 * j) /
        ((Nat.factorial (2 * j + 1) : ℚ) *
          (Nat.factorial (2 * (m - j) + 1) : ℚ))

lemma xi_time_part9zbj_lp_pf_rigidity_product_coeff_eq_explicit
    (phi : ℚ) (m : ℕ) :
    xi_time_part9zbj_lp_pf_rigidity_product_coeff phi m =
      xi_time_part9zbj_lp_pf_rigidity_explicit_coeff phi m := by
  rw [xi_time_part9zbj_lp_pf_rigidity_product_coeff,
    xi_time_part9zbj_lp_pf_rigidity_explicit_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : (4 : ℚ) ^ (m - j) * 4 ^ j = 4 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hjle]
  have hfact_left : (Nat.factorial (2 * (m - j) + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * (m - j) + 1)
  have hfact_right : (Nat.factorial (2 * j + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j + 1)
  have hfour : (4 : ℚ) ^ m ≠ 0 := by norm_num
  simp only [xi_time_part9zbj_lp_pf_rigidity_sinh_coeff, one_pow]
  field_simp [hpow, hfact_left, hfact_right, hfour, mul_assoc, mul_comm, mul_left_comm]
  rw [← hpow]
  ring

/-- Paper label: `thm:xi-time-part9zbj-lp-pf-rigidity`. -/
def xi_time_part9zbj_lp_pf_rigidity_statement : Prop :=
  (∀ phi : ℚ, ∀ m : ℕ,
    xi_time_part9zbj_lp_pf_rigidity_product_coeff phi m =
      xi_time_part9zbj_lp_pf_rigidity_explicit_coeff phi m) ∧
    xi_time_part9zbj_lp_pf_rigidity_product_coeff 3 2 =
      xi_time_part9zbj_lp_pf_rigidity_explicit_coeff 3 2

theorem paper_xi_time_part9zbj_lp_pf_rigidity :
    xi_time_part9zbj_lp_pf_rigidity_statement := by
  constructor
  · exact xi_time_part9zbj_lp_pf_rigidity_product_coeff_eq_explicit
  · exact xi_time_part9zbj_lp_pf_rigidity_product_coeff_eq_explicit 3 2

end Omega.Zeta
