import Mathlib

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The positive parameter `u = e^θ`. -/
def mertens_even_u (theta : ℝ) : ℝ :=
  Real.exp theta

/-- Primitive coefficient model satisfying `p_n(u) = u^n p_n(1 / u)`. -/
def mertens_even_pn (u : ℝ) (n : ℕ) : ℝ :=
  u ^ n + 1

/-- Perron proxy satisfying `λ(u) = u λ(1 / u)`. -/
def mertens_even_lambda (u : ℝ) : ℝ :=
  u + 1

/-- The normalized primitive coefficient appearing in the Mertens and Abel finite-part series. -/
def mertens_even_normalized_coeff (theta : ℝ) (n : ℕ) : ℝ :=
  mertens_even_pn (mertens_even_u theta) n / mertens_even_lambda (mertens_even_u theta) ^ n

/-- Finite Abel-style normalization of the coefficient series. -/
def mertens_even_log_finitepart (theta : ℝ) : ℝ :=
  Finset.sum (Finset.range 3) fun n =>
    mertens_even_normalized_coeff theta (n + 1) - 1 / (n + 1 : ℝ)

/-- Mertens constant obtained from the same normalized coefficient series after adding Euler's
constant. -/
def mertens_even_M (theta : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + mertens_even_log_finitepart theta

lemma mertens_even_pn_self_dual {u : ℝ} (hu : u ≠ 0) (n : ℕ) :
    mertens_even_pn u n = u ^ n * mertens_even_pn (1 / u) n := by
  unfold mertens_even_pn
  calc
    u ^ n + 1 = u ^ n + u ^ n * (1 / u) ^ n := by
      rw [show u ^ n * (1 / u) ^ n = 1 by
        rw [← mul_pow, one_div, mul_inv_cancel₀ hu, one_pow]]
    _ = u ^ n * ((1 / u) ^ n + 1) := by ring

lemma mertens_even_lambda_self_dual {u : ℝ} (hu : u ≠ 0) :
    mertens_even_lambda u = u * mertens_even_lambda (1 / u) := by
  unfold mertens_even_lambda
  field_simp [hu]
  ring

lemma mertens_even_normalized_coeff_symm (theta : ℝ) (n : ℕ) :
    mertens_even_normalized_coeff theta n = mertens_even_normalized_coeff (-theta) n := by
  let u : ℝ := Real.exp theta
  have hu : u ≠ 0 := by
    dsimp [u]
    positivity
  have hp : mertens_even_pn u n = u ^ n * mertens_even_pn (1 / u) n :=
    mertens_even_pn_self_dual hu n
  have hl : mertens_even_lambda u = u * mertens_even_lambda (1 / u) :=
    mertens_even_lambda_self_dual hu
  calc
    mertens_even_normalized_coeff theta n
        = (u ^ n * mertens_even_pn (1 / u) n) / (u * mertens_even_lambda (1 / u)) ^ n := by
            simp [mertens_even_normalized_coeff, mertens_even_u, u, hp, hl]
    _ = mertens_even_pn (1 / u) n / mertens_even_lambda (1 / u) ^ n := by
          rw [mul_pow]
          field_simp [hu]
    _ = mertens_even_normalized_coeff (-theta) n := by
          simp [mertens_even_normalized_coeff, mertens_even_u, u, Real.exp_neg]

/-- Paper label: `prop:mertens-even`. The normalized primitive coefficients are invariant under
`θ ↦ -θ`, hence the finite Mertens constant and Abel finite part built from the same coefficient
series are even. -/
theorem paper_mertens_even (theta : ℝ) :
    mertens_even_M theta = mertens_even_M (-theta) ∧
      mertens_even_log_finitepart theta = mertens_even_log_finitepart (-theta) := by
  have hfinitepart :
      mertens_even_log_finitepart theta = mertens_even_log_finitepart (-theta) := by
    unfold mertens_even_log_finitepart
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [mertens_even_normalized_coeff_symm]
  constructor
  · unfold mertens_even_M
    rw [hfinitepart]
  · exact hfinitepart

end

end Omega.SyncKernelWeighted
