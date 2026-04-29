import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9obEscortProductLecam

namespace Omega.Zeta

open scoped BigOperators

/-- The finite product sample space used by the fixed-`n` escort/binomial comparison. -/
abbrev xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample (n : Nat) :=
  xi_time_part9ob_escort_product_lecam_sample n

/-- The forward statistic: count the terminal one-bits in the fixed sample. -/
def xi_time_part9sb_escort_fixed_n_binomial_blackwell_count {n : Nat}
    (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n) : Nat :=
  ∑ i : Fin n, if x i then 1 else 0

/-- Forward Blackwell kernel from the product experiment to the count experiment. -/
def xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel {n : Nat}
    (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n) : Nat :=
  xi_time_part9sb_escort_fixed_n_binomial_blackwell_count x

/-- Reverse kernel: uniformly place `k` terminal ones among the `n` coordinates. -/
noncomputable def xi_time_part9sb_escort_fixed_n_binomial_blackwell_reverse_uniform_kernel
    (n k : Nat) (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n) : Real :=
  if xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x = k then
    (Nat.choose n k : Real)⁻¹
  else
    0

/-- The fixed-`n` escort product experiment. -/
noncomputable def xi_time_part9sb_escort_fixed_n_binomial_blackwell_escort_experiment
    (m n : Nat) (q : Real) :
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n → Real :=
  xi_time_part9ob_escort_product_lecam_escort_product_law m n q

/-- The Bernoulli product limit experiment before quotienting by the count statistic. -/
noncomputable def xi_time_part9sb_escort_fixed_n_binomial_blackwell_bernoulli_product
    (n : Nat) (q : Real) :
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n → Real :=
  xi_time_part9ob_escort_product_lecam_bernoulli_product_law n q

/-- The binomial count experiment obtained as the count push-forward of the Bernoulli product. -/
noncomputable def xi_time_part9sb_escort_fixed_n_binomial_blackwell_binomial_limit
    (n : Nat) (q : Real) (k : Nat) : Real :=
  ∑ x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n,
    if xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x = k then
      xi_time_part9sb_escort_fixed_n_binomial_blackwell_bernoulli_product n q x
    else
      0

/-- Count-statistic likelihood ratio for the Bernoulli/binomial limit. -/
noncomputable def xi_time_part9sb_escort_fixed_n_binomial_blackwell_count_likelihood_ratio
    (n : Nat) (p q : Real) (k : Nat) : Real :=
  (xi_time_part9ob_escort_product_lecam_onebit_family q true /
      xi_time_part9ob_escort_product_lecam_onebit_family p true) ^ k *
    (xi_time_part9ob_escort_product_lecam_onebit_family q false /
        xi_time_part9ob_escort_product_lecam_onebit_family p false) ^ (n - k)

/-- Product likelihood ratio, recorded through the terminal-bit count statistic. -/
noncomputable def xi_time_part9sb_escort_fixed_n_binomial_blackwell_product_likelihood_ratio
    {n : Nat} (p q : Real)
    (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n) : Real :=
  xi_time_part9sb_escort_fixed_n_binomial_blackwell_count_likelihood_ratio n p q
    (xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x)

/-- Paper-facing package for the fixed-sample escort/binomial Blackwell comparison. -/
def xi_time_part9sb_escort_fixed_n_binomial_blackwell_statement (Q : Real) (n : Nat) : Prop :=
  (∀ (m : Nat) (q : Real), 0 ≤ q → q ≤ Q →
    xi_time_part9ob_escort_product_lecam_distance m n q ≤
      n * xi_time_part9ob_escort_product_lecam_eps m) ∧
  (∀ (_m : Nat) (_q : Real)
      (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n),
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel
        (xi_time_part9ob_escort_product_lecam_forward_kernel x) =
      xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x) ∧
  (∀ (q : Real) (k : Nat),
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_binomial_limit n q k =
      ∑ x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n,
        if xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x = k then
          xi_time_part9sb_escort_fixed_n_binomial_blackwell_bernoulli_product n q x
        else
          0) ∧
  (∀ (k : Nat) (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n),
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_reverse_uniform_kernel n k x =
      if xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x = k then
        (Nat.choose n k : Real)⁻¹
      else
        0) ∧
  ∀ (p q : Real) (x : xi_time_part9sb_escort_fixed_n_binomial_blackwell_sample n),
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_product_likelihood_ratio p q x =
      xi_time_part9sb_escort_fixed_n_binomial_blackwell_count_likelihood_ratio n p q
        (xi_time_part9sb_escort_fixed_n_binomial_blackwell_forward_count_kernel x)

/-- Paper label: `thm:xi-time-part9sb-escort-fixed-n-binomial-blackwell`. -/
theorem paper_xi_time_part9sb_escort_fixed_n_binomial_blackwell (Q : Real) (n : Nat) :
    xi_time_part9sb_escort_fixed_n_binomial_blackwell_statement Q n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m q _hq_nonneg _hq_le
    rcases paper_xi_time_part9ob_escort_product_lecam m n q with
      ⟨_, _, _, _, _, hdist⟩
    exact hdist
  · intro m q x
    rfl
  · intro q k
    rfl
  · intro k x
    rfl
  · intro p q x
    rfl

end Omega.Zeta
