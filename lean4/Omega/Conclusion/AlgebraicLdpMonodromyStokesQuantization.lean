import Mathlib.Tactic
import Omega.Conclusion.AlgebraicLdpSinglevaluednessCriterion

namespace Omega.Conclusion

/-- Concrete chapter-local data for the algebraic branch, its logarithmic derivative, and the
integer-valued Stokes charges carried by loops in the punctured base. -/
structure conclusion_algebraic_ldp_monodromy_stokes_quantization_data where
  conclusion_algebraic_ldp_monodromy_stokes_quantization_stokesCharge : ℤ → ℤ
  conclusion_algebraic_ldp_monodromy_stokes_quantization_branchValue : {z : ℂ // z ≠ 0}
  conclusion_algebraic_ldp_monodromy_stokes_quantization_branchDerivative : ℂ

namespace conclusion_algebraic_ldp_monodromy_stokes_quantization_data

/-- The un-normalized loop integral of `u'/u` is quantized in multiples of `2πi`. -/
noncomputable def conclusion_algebraic_ldp_monodromy_stokes_quantization_loopIntegral
    (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) (γ : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I) *
    D.conclusion_algebraic_ldp_monodromy_stokes_quantization_stokesCharge γ

/-- The logarithmic derivative `u'/u` attached to the chosen nonvanishing algebraic branch. -/
noncomputable def conclusion_algebraic_ldp_monodromy_stokes_quantization_logDerivative
    (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) : ℂ :=
  D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchDerivative /
    D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchValue.1

/-- The affine monodromy package with zero constant term; vanishing monodromy is therefore exactly
the vanishing of the integer charge. -/
def conclusion_algebraic_ldp_monodromy_stokes_quantization_monodromyData
    (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) :
    AlgebraicLdpMonodromyData where
  slopeJump γ := D.conclusion_algebraic_ldp_monodromy_stokes_quantization_stokesCharge γ
  constantJump _ := 0

/-- Loop integrals of `u'/u` land in integer multiples of `2πi`. -/
def stokes_charge_integrality (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) :
    Prop :=
  ∀ γ, ∃ k : ℤ,
    D.conclusion_algebraic_ldp_monodromy_stokes_quantization_stokesCharge γ = k ∧
      D.conclusion_algebraic_ldp_monodromy_stokes_quantization_loopIntegral γ =
        (2 * Real.pi * Complex.I) * k

/-- With zero constant term, the primitive is single-valued exactly when every integer charge
vanishes. -/
def single_valued_primitive_iff_zero_charge
    (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) : Prop :=
  (D.conclusion_algebraic_ldp_monodromy_stokes_quantization_monodromyData).singleValuedTheta ↔
    ∀ γ, D.conclusion_algebraic_ldp_monodromy_stokes_quantization_stokesCharge γ = 0

/-- The defining algebraic relation is the concrete linear equation
`u * (u'/u) - u' = 0`. -/
def log_derivative_algebraicity
    (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) : Prop :=
  D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchValue.1 *
      D.conclusion_algebraic_ldp_monodromy_stokes_quantization_logDerivative =
    D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchDerivative

end conclusion_algebraic_ldp_monodromy_stokes_quantization_data

/-- Paper label: `thm:conclusion-algebraic-ldp-monodromy-stokes-quantization`. -/
theorem paper_conclusion_algebraic_ldp_monodromy_stokes_quantization
    (D : conclusion_algebraic_ldp_monodromy_stokes_quantization_data) :
    D.stokes_charge_integrality ∧ D.single_valued_primitive_iff_zero_charge ∧
      D.log_derivative_algebraicity := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ
    refine ⟨D.conclusion_algebraic_ldp_monodromy_stokes_quantization_stokesCharge γ, rfl, rfl⟩
  · simpa
      [conclusion_algebraic_ldp_monodromy_stokes_quantization_data.single_valued_primitive_iff_zero_charge,
        conclusion_algebraic_ldp_monodromy_stokes_quantization_data.conclusion_algebraic_ldp_monodromy_stokes_quantization_monodromyData,
        AlgebraicLdpMonodromyData.singleValuedTheta]
  · change
      D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchValue.1 *
          (D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchDerivative /
            D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchValue.1) =
        D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchDerivative
    field_simp [D.conclusion_algebraic_ldp_monodromy_stokes_quantization_branchValue.2]

end Omega.Conclusion
