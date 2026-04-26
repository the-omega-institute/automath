import Mathlib.Tactic
import Omega.Conclusion.FibadicGcdConvolutionDiagonalization
import Omega.Conclusion.FibadicHaarConditionalExpectationConvolution
import Omega.Conclusion.FibadicPrimitiveCentralIdempotents

namespace Omega.Conclusion

open scoped BigOperators

/-- Rational coefficient model for the random-depth spectral criterion. -/
abbrev conclusion_fibadic_random_depth_average_spectral_criterion_coefficient := ℕ → ℚ

/-- The exact-depth projector used in the finite random-depth average. -/
def conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_projector
    (d : ℕ) (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) :
    conclusion_fibadic_random_depth_average_spectral_criterion_coefficient :=
  fun n => if n ∣ d then f n else 0

/-- A coefficient vector supported on a single exact-depth block. -/
def conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_block
    (g : ℕ) (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) :
    Prop :=
  ∀ n, f n ≠ 0 → n = g

/-- Finite support for the rational coefficient model. -/
def conclusion_fibadic_random_depth_average_spectral_criterion_finite_support
    (S : Finset ℕ)
    (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) : Prop :=
  ∀ n, n ∉ S → f n = 0

/-- The finite random-depth averaging operator, a rational linear combination of exact-depth
projectors. -/
def conclusion_fibadic_random_depth_average_spectral_criterion_operator
    (depths : Finset ℕ) (weight : ℕ → ℚ)
    (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) :
    conclusion_fibadic_random_depth_average_spectral_criterion_coefficient :=
  fun n =>
    depths.sum fun d =>
      weight d *
        conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_projector d f n

/-- Spectral multiplier seen by an exact-depth block of depth `g`. -/
def conclusion_fibadic_random_depth_average_spectral_criterion_multiplier
    (depths : Finset ℕ) (weight : ℕ → ℚ) (g : ℕ) : ℚ :=
  depths.sum fun d => weight d * if g ∣ d then 1 else 0

lemma conclusion_fibadic_random_depth_average_spectral_criterion_operator_apply_block
    (depths : Finset ℕ) (weight : ℕ → ℚ)
    (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) (g n : ℕ)
    (hblock : conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_block g f) :
    conclusion_fibadic_random_depth_average_spectral_criterion_operator depths weight f n =
      conclusion_fibadic_random_depth_average_spectral_criterion_multiplier depths weight g *
        f n := by
  by_cases hfn : f n = 0
  · simp [conclusion_fibadic_random_depth_average_spectral_criterion_operator,
      conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_projector,
      conclusion_fibadic_random_depth_average_spectral_criterion_multiplier, hfn]
  · have hng : n = g := hblock n hfn
    subst n
    rw [conclusion_fibadic_random_depth_average_spectral_criterion_operator,
      conclusion_fibadic_random_depth_average_spectral_criterion_multiplier, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro d hd
    by_cases hgd : g ∣ d <;>
      simp [conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_projector, hgd]

lemma conclusion_fibadic_random_depth_average_spectral_criterion_operator_block
    (depths : Finset ℕ) (weight : ℕ → ℚ)
    (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) (g : ℕ)
    (hblock : conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_block g f) :
    conclusion_fibadic_random_depth_average_spectral_criterion_operator depths weight f =
      fun n =>
        conclusion_fibadic_random_depth_average_spectral_criterion_multiplier depths weight g *
          f n := by
  funext n
  exact
    conclusion_fibadic_random_depth_average_spectral_criterion_operator_apply_block depths weight
      f g n hblock

lemma conclusion_fibadic_random_depth_average_spectral_criterion_operator_finite_support
    (S depths : Finset ℕ) (weight : ℕ → ℚ)
    (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient)
    (hf : conclusion_fibadic_random_depth_average_spectral_criterion_finite_support S f) :
    conclusion_fibadic_random_depth_average_spectral_criterion_finite_support S
      (conclusion_fibadic_random_depth_average_spectral_criterion_operator depths weight f) := by
  intro n hn
  have hfn : f n = 0 := hf n hn
  simp [conclusion_fibadic_random_depth_average_spectral_criterion_operator,
    conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_projector, hfn]

/-- Concrete spectral criterion for finite random-depth averaging: the gcd-convolution package is
available, finite support is preserved, exact-depth blocks are eigenvectors, and the corresponding
eigenvalue is the finite convex coefficient sum over depths divisible by the block depth. -/
def conclusion_fibadic_random_depth_average_spectral_criterion_statement : Prop :=
  conclusion_fibadic_gcd_convolution_diagonalization_statement ∧
    (∀ (S depths : Finset ℕ) (weight : ℕ → ℚ)
      (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient),
        conclusion_fibadic_random_depth_average_spectral_criterion_finite_support S f →
          conclusion_fibadic_random_depth_average_spectral_criterion_finite_support S
            (conclusion_fibadic_random_depth_average_spectral_criterion_operator depths weight f)) ∧
    (∀ (depths : Finset ℕ) (weight : ℕ → ℚ)
      (f : conclusion_fibadic_random_depth_average_spectral_criterion_coefficient) (g : ℕ),
        conclusion_fibadic_random_depth_average_spectral_criterion_exact_depth_block g f →
          conclusion_fibadic_random_depth_average_spectral_criterion_operator depths weight f =
            fun n =>
              conclusion_fibadic_random_depth_average_spectral_criterion_multiplier depths weight g *
                f n) ∧
    (∀ (depths : Finset ℕ) (weight : ℕ → ℚ) (g : ℕ),
      conclusion_fibadic_random_depth_average_spectral_criterion_multiplier depths weight g =
        depths.sum fun d => weight d * if g ∣ d then 1 else 0)

/-- Paper label: `thm:conclusion-fibadic-random-depth-average-spectral-criterion`. -/
theorem paper_conclusion_fibadic_random_depth_average_spectral_criterion :
    conclusion_fibadic_random_depth_average_spectral_criterion_statement := by
  refine ⟨paper_conclusion_fibadic_gcd_convolution_diagonalization, ?_, ?_, ?_⟩
  · intro S depths weight f hf
    exact
      conclusion_fibadic_random_depth_average_spectral_criterion_operator_finite_support S depths
        weight f hf
  · intro depths weight f g hblock
    exact
      conclusion_fibadic_random_depth_average_spectral_criterion_operator_block depths weight f g
        hblock
  · intro depths weight g
    rfl

end Omega.Conclusion
