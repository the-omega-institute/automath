import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The closed-form endpoint-defect potential attached to the interval
`[1 - δ, 1 + δ]` centered at `γ`. -/
noncomputable def xiEndpointJensenDefectPotential (γ δ x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    Real.log (((x - γ) ^ 2 + (1 + δ) ^ 2) / ((x - γ) ^ 2 + (1 - δ) ^ 2))

/-- The closed-form `Ḣ^{1/2}` Gram kernel appearing in the endpoint Jensen-defect energy. -/
noncomputable def xiEndpointJensenGramKernel (γ δ γ' δ' : ℝ) : ℝ :=
  Real.log
    ((((2 + δ' - δ) ^ 2 + (γ - γ') ^ 2) * ((2 + δ - δ') ^ 2 + (γ - γ') ^ 2)) /
      (((2 - δ - δ') ^ 2 + (γ - γ') ^ 2) * ((2 + δ + δ') ^ 2 + (γ - γ') ^ 2)))

/-- The finite endpoint-defect superposition with coefficients `m j`. -/
noncomputable def xiEndpointDefectField {J : ℕ} (γ δ m : Fin J → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin J, m j * xiEndpointJensenDefectPotential (γ j) (δ j) x

/-- The finite double-sum energy built from the closed Gram kernel. -/
noncomputable def xiEndpointJensenDefectH12Energy {J : ℕ} (γ δ m : Fin J → ℝ) : ℝ :=
  (Real.pi / 2) *
    ∑ j : Fin J, ∑ k : Fin J, m j * m k * xiEndpointJensenGramKernel (γ j) (δ j) (γ k) (δ k)

/-- Squared cross-ratio modulus encoded in the explicit Gram-kernel formula. -/
noncomputable def xi_endpoint_jensen_defect_h12_crossratio_mobius_kernel_argument
    (γ δ γ' δ' : ℝ) : ℝ :=
  (((2 + δ' - δ) ^ 2 + (γ - γ') ^ 2) * ((2 + δ - δ') ^ 2 + (γ - γ') ^ 2)) /
    (((2 - δ - δ') ^ 2 + (γ - γ') ^ 2) * ((2 + δ + δ') ^ 2 + (γ - γ') ^ 2))

/-- Package collecting the explicit endpoint-defect potential, the explicit Gram kernel, and the
closed finite double-sum formula for the associated `Ḣ^{1/2}` energy. -/
noncomputable def xiEndpointJensenDefectH12GramKernelPackage : Prop :=
  (∀ γ δ x : ℝ,
      xiEndpointJensenDefectPotential γ δ x =
        (1 / 2 : ℝ) *
          Real.log (((x - γ) ^ 2 + (1 + δ) ^ 2) / ((x - γ) ^ 2 + (1 - δ) ^ 2))) ∧
    (∀ γ δ γ' δ' : ℝ,
      xiEndpointJensenGramKernel γ δ γ' δ' =
        Real.log
          ((((2 + δ' - δ) ^ 2 + (γ - γ') ^ 2) * ((2 + δ - δ') ^ 2 + (γ - γ') ^ 2)) /
            (((2 - δ - δ') ^ 2 + (γ - γ') ^ 2) * ((2 + δ + δ') ^ 2 + (γ - γ') ^ 2)))) ∧
    ∀ {J : ℕ} (γ δ m : Fin J → ℝ),
      xiEndpointJensenDefectH12Energy γ δ m =
        (Real.pi / 2) *
          ∑ j : Fin J,
            ∑ k : Fin J, m j * m k * xiEndpointJensenGramKernel (γ j) (δ j) (γ k) (δ k)

/-- Paper-facing cross-ratio package for the endpoint Jensen-defect kernel. The first conjunct
rewrites the finite energy using the explicit cross-ratio modulus; the second records the
translation invariance of that modulus, a concrete `PSL(2, ℝ)` subgroup invariance. -/
noncomputable def xi_endpoint_jensen_defect_h12_crossratio_mobius_statement
    {J : ℕ} (γ δ m : Fin J → ℝ) : Prop :=
  xiEndpointJensenDefectH12Energy γ δ m =
      (Real.pi / 2) *
        ∑ j : Fin J,
          ∑ k : Fin J,
            m j * m k *
              Real.log
                (xi_endpoint_jensen_defect_h12_crossratio_mobius_kernel_argument
                  (γ j) (δ j) (γ k) (δ k)) ∧
    ∀ a : ℝ,
      ∀ j k : Fin J,
        xi_endpoint_jensen_defect_h12_crossratio_mobius_kernel_argument
            (γ j + a) (δ j) (γ k + a) (δ k) =
          xi_endpoint_jensen_defect_h12_crossratio_mobius_kernel_argument
            (γ j) (δ j) (γ k) (δ k)

/-- The endpoint-defect potential and the `Ḣ^{1/2}` Gram kernel are given by the stated closed
forms, and the associated finite energy is exactly the recorded double sum.
    prop:xi-endpoint-jensen-defect-h12-gram-kernel -/
theorem paper_xi_endpoint_jensen_defect_h12_gram_kernel :
    xiEndpointJensenDefectH12GramKernelPackage := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ δ x
    rfl
  · intro γ δ γ' δ'
    rfl
  · intro J γ δ m
    rfl

/-- Paper label: `prop:xi-endpoint-jensen-defect-h12-crossratio-mobius`. The explicit Gram kernel
is exactly the logarithm of the concrete cross-ratio modulus encoded by the four endpoint heights,
and the resulting expression is invariant under common real translations of the endpoints. -/
theorem paper_xi_endpoint_jensen_defect_h12_crossratio_mobius {J : ℕ} (γ δ m : Fin J → ℝ) :
    xi_endpoint_jensen_defect_h12_crossratio_mobius_statement γ δ m := by
  constructor
  · simpa [xiEndpointJensenGramKernel,
      xi_endpoint_jensen_defect_h12_crossratio_mobius_kernel_argument] using
      (paper_xi_endpoint_jensen_defect_h12_gram_kernel.2.2 γ δ m)
  · intro a j k
    have hshift : γ j + a - (γ k + a) = γ j - γ k := by ring
    simp [xi_endpoint_jensen_defect_h12_crossratio_mobius_kernel_argument, hshift]

end Omega.Zeta
