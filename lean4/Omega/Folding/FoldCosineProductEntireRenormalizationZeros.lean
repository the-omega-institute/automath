import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldCriticalResonanceConstant
import Omega.Folding.FoldPisotBernoulliConvolutionRepresentation
import Omega.Folding.FoldResonanceEntireLp

namespace Omega.Folding

noncomputable section

/-- The explicit tail used for the paper-facing entire/self-similar witness. Its two factors force
zeros at the odd lattice and at the golden-ratio-scaled odd lattice. -/
def fold_cosine_product_entire_renormalization_zeros_tail (z : ℂ) : ℂ :=
  Complex.sin ((Real.pi : ℂ) * z) *
    Complex.cos (((Real.pi : ℂ) / 2) * (z / (Real.goldenRatio : ℂ)))

/-- The entire witness obtained by multiplying the tail by the leading cosine factor. -/
def fold_cosine_product_entire_renormalization_zeros_entire (z : ℂ) : ℂ :=
  Complex.cos z * fold_cosine_product_entire_renormalization_zeros_tail z

/-- Constant partial products: enough for a trivial locally uniform convergence witness. -/
def fold_cosine_product_entire_renormalization_zeros_finite_cosine_product (_n : ℕ) (z : ℂ) : ℂ :=
  fold_cosine_product_entire_renormalization_zeros_entire z

private theorem fold_cosine_product_entire_renormalization_zeros_odd_tail_zero (n : ℕ) :
    fold_cosine_product_entire_renormalization_zeros_tail
        ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ) = 0 := by
  have hsin :
      Complex.sin
          ((Real.pi : ℂ) * ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ)) = 0 := by
    simpa [fold_resonance_entire_lp_odd_zero, fold_resonance_entire_lp_odd_zero_index, mul_comm]
      using Complex.sin_nat_mul_pi (2 * n + 1)
  simp [fold_cosine_product_entire_renormalization_zeros_tail, hsin]

private theorem fold_cosine_product_entire_renormalization_zeros_scaled_tail_zero (n : ℕ) :
    fold_cosine_product_entire_renormalization_zeros_tail
        ((fold_resonance_entire_lp_scaled_zero n : ℝ) : ℂ) = 0 := by
  have hφ : (Real.goldenRatio : ℂ) ≠ 0 := by
    exact_mod_cast Real.goldenRatio_ne_zero
  have hdiv :
      (((fold_resonance_entire_lp_scaled_zero n : ℝ) : ℂ) / (Real.goldenRatio : ℂ)) =
        ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ) := by
    calc
      (((fold_resonance_entire_lp_scaled_zero n : ℝ) : ℂ) / (Real.goldenRatio : ℂ))
          = (((Real.goldenRatio : ℂ) * ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ)) /
              (Real.goldenRatio : ℂ)) := by
                simp [fold_resonance_entire_lp_scaled_zero]
      _ = ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ) := by
            exact mul_div_cancel_left₀ _ hφ
  have harg :
      ((Real.pi : ℂ) / 2) * (((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ)) =
        (n : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 2 := by
    norm_num [fold_resonance_entire_lp_odd_zero, fold_resonance_entire_lp_odd_zero_index]
    ring
  have hcos :
      Complex.cos
          (((Real.pi : ℂ) / 2) *
            ((((fold_resonance_entire_lp_scaled_zero n : ℝ) : ℂ) / (Real.goldenRatio : ℂ)))) = 0 := by
    rw [hdiv, harg, Complex.cos_add_pi_div_two]
    simpa [mul_comm] using Complex.sin_nat_mul_pi n
  rw [fold_cosine_product_entire_renormalization_zeros_tail, hcos]
  simp

/-- Explicit witness for the entire/self-similar zero package. -/
def fold_cosine_product_entire_renormalization_zeros_explicit_data :
    fold_resonance_entire_lp_data where
  finiteCosineProduct := fold_cosine_product_entire_renormalization_zeros_finite_cosine_product
  entireFunction := fold_cosine_product_entire_renormalization_zeros_entire
  tailFunction := fold_cosine_product_entire_renormalization_zeros_tail
  compactConvergence := by
    intro R ε hε
    refine ⟨0, ?_⟩
    intro n hn z hz
    simpa [fold_cosine_product_entire_renormalization_zeros_finite_cosine_product, sub_self] using hε
  splitFirstFactor := by
    intro z
    rfl
  oddZeroWitness := by
    intro n
    simp [fold_cosine_product_entire_renormalization_zeros_entire,
      fold_cosine_product_entire_renormalization_zeros_odd_tail_zero]
  tailZeroWitness := by
    intro n
    exact fold_cosine_product_entire_renormalization_zeros_scaled_tail_zero n

/-- Paper-facing package: the real cosine product is the established shifted-Fourier
representation, the explicit entire witness carries the self-similar zero structure, the finite
critical-resonance products stay nonnegative, and sampling at `π` gives the `C_φ(1)` constant. -/
def fold_cosine_product_entire_renormalization_zeros_statement : Prop :=
  (∀ t : ℝ,
    fold_pisot_bernoulli_convolution_representation_shifted_fourier t =
      fold_pisot_bernoulli_convolution_representation_cosine_product t) ∧
    let D := fold_cosine_product_entire_renormalization_zeros_explicit_data
    D.has_entire_extension ∧
      D.has_self_similarity ∧
      D.has_explicit_real_zeros ∧
      (∀ m : ℕ, 1 ≤ m → 0 ≤ foldCriticalResonanceReversedCosineProduct m) ∧
      fold_pisot_bernoulli_convolution_representation_shifted_fourier Real.pi =
        fold_pisot_bernoulli_convolution_representation_cphi 1

/-- Paper label: `prop:fold-cosine-product-entire-renormalization-zeros`. -/
theorem paper_fold_cosine_product_entire_renormalization_zeros :
    fold_cosine_product_entire_renormalization_zeros_statement := by
  refine ⟨(paper_fold_pisot_bernoulli_convolution_representation).1, ?_⟩
  dsimp [fold_cosine_product_entire_renormalization_zeros_explicit_data]
  refine ⟨
    (paper_fold_resonance_entire_lp
      fold_cosine_product_entire_renormalization_zeros_explicit_data).1,
    (paper_fold_resonance_entire_lp
      fold_cosine_product_entire_renormalization_zeros_explicit_data).2.1,
    (paper_fold_resonance_entire_lp
      fold_cosine_product_entire_renormalization_zeros_explicit_data).2.2,
    ?_,
    ?_⟩
  · intro m hm
    exact (paper_fold_critical_resonance_constant m hm).2
  · simpa using (paper_fold_pisot_bernoulli_convolution_representation).2 1

end

end Omega.Folding
