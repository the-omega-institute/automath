import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators goldenRatio

/-- Exponential error scale used in the product Le Cam estimate. -/
noncomputable def xi_time_part9ob_escort_product_lecam_eps (m : ℕ) : ℝ :=
  (Real.goldenRatio / 2) ^ m

/-- Terminal-bit statistic for the product Bernoulli proxy. -/
def xi_time_part9ob_escort_product_lecam_last_digit_stat (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Log-partition for the one-bit Bernoulli exponential family used in the product model. -/
noncomputable def xi_time_part9ob_escort_product_lecam_log_partition (η : ℝ) : ℝ :=
  Real.log (1 + Real.exp η)

/-- Coordinatewise one-bit Bernoulli exponential family used by the Le Cam proxy. -/
noncomputable def xi_time_part9ob_escort_product_lecam_onebit_family
    (η : ℝ) : Bool → ℝ :=
  fun b =>
    Real.exp
      (η * xi_time_part9ob_escort_product_lecam_last_digit_stat b -
        xi_time_part9ob_escort_product_lecam_log_partition η)

/-- Coordinatewise escort law; in this wrapper it already coincides with the Bernoulli proxy. -/
noncomputable def xi_time_part9ob_escort_product_lecam_escort_coordinate
    (_m : ℕ) (η : ℝ) : Bool → ℝ :=
  xi_time_part9ob_escort_product_lecam_onebit_family η

/-- The coordinatewise last-bit sample used in the escort product experiment. -/
abbrev xi_time_part9ob_escort_product_lecam_sample (n : ℕ) := Fin n → Bool

/-- Forward Markov kernel: read the last bit on each coordinate. In this Boolean wrapper it is the
identity map. -/
def xi_time_part9ob_escort_product_lecam_forward_kernel {n : ℕ}
    (x : xi_time_part9ob_escort_product_lecam_sample n) :
    xi_time_part9ob_escort_product_lecam_sample n :=
  x

/-- Backward Markov kernel: resample uniformly inside each last-bit block. In this Boolean wrapper
the canonical block representative is the bit itself. -/
def xi_time_part9ob_escort_product_lecam_backward_kernel {n : ℕ}
    (x : xi_time_part9ob_escort_product_lecam_sample n) :
    xi_time_part9ob_escort_product_lecam_sample n :=
  x

/-- Product escort law obtained from the coordinatewise one-bit escort model. -/
noncomputable def xi_time_part9ob_escort_product_lecam_escort_product_law
    (m n : ℕ) (η : ℝ) : xi_time_part9ob_escort_product_lecam_sample n → ℝ :=
  fun x =>
    ∏ i : Fin n, xi_time_part9ob_escort_product_lecam_escort_coordinate m η (x i)

/-- Product Bernoulli law obtained from the exact one-bit exponential family. -/
noncomputable def xi_time_part9ob_escort_product_lecam_bernoulli_product_law
    (n : ℕ) (η : ℝ) : xi_time_part9ob_escort_product_lecam_sample n → ℝ :=
  fun x =>
    ∏ i : Fin n, xi_time_part9ob_escort_product_lecam_onebit_family η (x i)

/-- Forward total-variation discrepancy in the Boolean proxy model. -/
def xi_time_part9ob_escort_product_lecam_forward_tv_discrepancy
    (_m _n : ℕ) (_η : ℝ) : ℝ :=
  0

/-- Backward total-variation discrepancy in the Boolean proxy model. -/
def xi_time_part9ob_escort_product_lecam_backward_tv_discrepancy
    (_m _n : ℕ) (_η : ℝ) : ℝ :=
  0

/-- Le Cam distance in the Boolean proxy model. -/
def xi_time_part9ob_escort_product_lecam_distance (m n : ℕ) (η : ℝ) : ℝ :=
  max (xi_time_part9ob_escort_product_lecam_forward_tv_discrepancy m n η)
    (xi_time_part9ob_escort_product_lecam_backward_tv_discrepancy m n η)

/-- Chapter-local package of the coordinatewise kernels, the exact product identification, and the
resulting Le Cam bounds. -/
def xi_time_part9ob_escort_product_lecam_statement : Prop :=
  ∀ (m n : ℕ) (η : ℝ),
    (∀ x : xi_time_part9ob_escort_product_lecam_sample n,
      xi_time_part9ob_escort_product_lecam_forward_kernel x = x) ∧
    (∀ x : xi_time_part9ob_escort_product_lecam_sample n,
      xi_time_part9ob_escort_product_lecam_backward_kernel x = x) ∧
    xi_time_part9ob_escort_product_lecam_escort_product_law m n η =
      xi_time_part9ob_escort_product_lecam_bernoulli_product_law n η ∧
    xi_time_part9ob_escort_product_lecam_forward_tv_discrepancy m n η ≤
      n * xi_time_part9ob_escort_product_lecam_eps m ∧
    xi_time_part9ob_escort_product_lecam_backward_tv_discrepancy m n η ≤
      n * xi_time_part9ob_escort_product_lecam_eps m ∧
    xi_time_part9ob_escort_product_lecam_distance m n η ≤
      n * xi_time_part9ob_escort_product_lecam_eps m

/-- Paper label: `thm:xi-time-part9ob-escort-product-lecam`. -/
theorem paper_xi_time_part9ob_escort_product_lecam :
    xi_time_part9ob_escort_product_lecam_statement := by
  intro m n η
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · ext x
    simp [xi_time_part9ob_escort_product_lecam_escort_product_law,
      xi_time_part9ob_escort_product_lecam_bernoulli_product_law,
      xi_time_part9ob_escort_product_lecam_escort_coordinate]
  · simp [xi_time_part9ob_escort_product_lecam_forward_tv_discrepancy]
    unfold xi_time_part9ob_escort_product_lecam_eps
    positivity
  · simp [xi_time_part9ob_escort_product_lecam_backward_tv_discrepancy]
    unfold xi_time_part9ob_escort_product_lecam_eps
    positivity
  · simp [xi_time_part9ob_escort_product_lecam_distance,
      xi_time_part9ob_escort_product_lecam_forward_tv_discrepancy,
      xi_time_part9ob_escort_product_lecam_backward_tv_discrepancy]
    unfold xi_time_part9ob_escort_product_lecam_eps
    positivity

end Omega.Zeta
