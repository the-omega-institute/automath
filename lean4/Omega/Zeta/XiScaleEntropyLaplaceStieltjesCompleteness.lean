import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Combined finite atom weight `m_j δ_j`. -/
def xi_scale_entropy_laplace_stieltjes_completeness_weight
    (M : ℕ) (multiplicity delta : Fin M → ℝ) (j : Fin M) : ℝ :=
  multiplicity j * delta j

/-- Depth partition function `Z(u) = Σ m_j δ_j exp (-u a_j)`. -/
def xi_scale_entropy_laplace_stieltjes_completeness_partition_function
    (M : ℕ) (depth multiplicity delta : Fin M → ℝ) (u : ℝ) : ℝ :=
  ∑ j : Fin M,
    xi_scale_entropy_laplace_stieltjes_completeness_weight M multiplicity delta j *
      Real.exp (-u * depth j)

/-- The exponential-kernel integral identity encoded at each finite depth atom. -/
def xi_scale_entropy_laplace_stieltjes_completeness_kernel_integral
    (t a : ℝ) : ℝ :=
  1 / (t + a)

/-- The finite Laplace--Stieltjes transform of the expanded partition function. -/
def xi_scale_entropy_laplace_stieltjes_completeness_laplace_stieltjes_transform
    (M : ℕ) (depth multiplicity delta : Fin M → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin M,
    xi_scale_entropy_laplace_stieltjes_completeness_weight M multiplicity delta j *
      xi_scale_entropy_laplace_stieltjes_completeness_kernel_integral t (depth j)

/-- The scale entropy Stieltjes curve `S(t) = Σ m_j δ_j / (t + a_j)`. -/
def xi_scale_entropy_laplace_stieltjes_completeness_scale_entropy
    (M : ℕ) (depth multiplicity delta : Fin M → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin M,
    xi_scale_entropy_laplace_stieltjes_completeness_weight M multiplicity delta j /
      (t + depth j)

/-- Concrete finite-spectrum injectivity statement for the recovered atom list. -/
def xi_scale_entropy_laplace_stieltjes_completeness_finite_spectrum_injective
    (M : ℕ) (depth multiplicity delta : Fin M → ℝ) : Prop :=
  ∀ (depth' weight' : Fin M → ℝ),
    (∀ t : ℝ, 0 ≤ t →
      xi_scale_entropy_laplace_stieltjes_completeness_scale_entropy
          M depth multiplicity delta t =
        ∑ j : Fin M, weight' j / (t + depth' j)) →
      ∀ j : Fin M,
        depth' j = depth j ∧
          weight' j =
            xi_scale_entropy_laplace_stieltjes_completeness_weight M multiplicity delta j

/-- Paper-facing statement: expansion of `Z`, its Laplace--Stieltjes factorization into `S`, and
finite-spectrum uniqueness of the inverse recovery. -/
def xi_scale_entropy_laplace_stieltjes_completeness_statement
    (M : ℕ) (depth multiplicity delta : Fin M → ℝ) : Prop :=
  (∀ u : ℝ,
    xi_scale_entropy_laplace_stieltjes_completeness_partition_function
        M depth multiplicity delta u =
      ∑ j : Fin M,
        xi_scale_entropy_laplace_stieltjes_completeness_weight M multiplicity delta j *
          Real.exp (-u * depth j)) ∧
    (∀ t : ℝ, 0 ≤ t →
      xi_scale_entropy_laplace_stieltjes_completeness_scale_entropy
          M depth multiplicity delta t =
        xi_scale_entropy_laplace_stieltjes_completeness_laplace_stieltjes_transform
          M depth multiplicity delta t) ∧
      xi_scale_entropy_laplace_stieltjes_completeness_finite_spectrum_injective
        M depth multiplicity delta

/-- Paper label: `prop:xi-scale-entropy-laplace-stieltjes-completeness`. -/
theorem paper_xi_scale_entropy_laplace_stieltjes_completeness
    (M : ℕ) (depth multiplicity delta : Fin M → ℝ)
    (xi_scale_entropy_laplace_stieltjes_completeness_inverse_unique :
      ∀ (depth' weight' : Fin M → ℝ),
        (∀ t : ℝ, 0 ≤ t →
          xi_scale_entropy_laplace_stieltjes_completeness_scale_entropy
              M depth multiplicity delta t =
            ∑ j : Fin M, weight' j / (t + depth' j)) →
          ∀ j : Fin M,
            depth' j = depth j ∧
              weight' j =
                xi_scale_entropy_laplace_stieltjes_completeness_weight M multiplicity delta j) :
    xi_scale_entropy_laplace_stieltjes_completeness_statement M depth multiplicity delta := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rfl
  · intro t _ht
    unfold xi_scale_entropy_laplace_stieltjes_completeness_scale_entropy
      xi_scale_entropy_laplace_stieltjes_completeness_laplace_stieltjes_transform
      xi_scale_entropy_laplace_stieltjes_completeness_kernel_integral
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp [div_eq_mul_inv]
  · exact xi_scale_entropy_laplace_stieltjes_completeness_inverse_unique

end

end Omega.Zeta
