import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
import Omega.Zeta.XiTimePart62eaDualfingerprintBooleanStrongProductLaw

namespace Omega.Zeta

/-- The `S₁₀` component used by the parity-neutral finite product model. -/
abbrev xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S10 :=
  xi_time_part62ea_dualfingerprint_boolean_strong_product_law_G10

/-- The `S₃` splitting component used by the parity-neutral finite product model. -/
abbrev xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3 :=
  xi_time_part62ea_dualfingerprint_boolean_strong_product_law_G3

/-- Uniform density of an `S₃` event in the finite splitting component. -/
def xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_s3_density
    (D : Finset xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3) : ℚ :=
  (D.card : ℚ) /
    (Fintype.card xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3 : ℚ)

/-- The sign half-density supplied by the `S₁₀` parity split. -/
def xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_sign_half_density : ℚ :=
  1 / 2

/-- Product density after imposing the `S₁₀` sign event and an arbitrary `S₃` event. -/
def xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_product_density
    (D : Finset xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3) : ℚ :=
  xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_sign_half_density *
    xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_s3_density D

/-- Conditional density of the `S₃` event after dividing by the positive sign half-density. -/
def xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_conditional_density
    (D : Finset xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3) : ℚ :=
  xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_product_density D /
    xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_sign_half_density

/-- Imported strong product-law wrapper for the same `S₁₀ × S₃` finite product context. -/
theorem xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_imported_product_law
    (C : xi_time_part62ea_dualfingerprint_boolean_strong_product_law_Context)
    (hC : C.class_function_tensor_independence) :
    C.boolean_product_law :=
  paper_xi_time_part62ea_dualfingerprint_boolean_strong_product_law C hC

/-- Concrete parity-neutrality statement for conditioning on the `S₁₀` sign event. -/
def xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_statement : Prop :=
  ∀ D : Finset xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3,
    0 < xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_sign_half_density ∧
      Fintype.card xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3 = 6 ∧
      xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_s3_density D =
        (D.card : ℚ) / 6 ∧
      xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_conditional_density D =
        xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_s3_density D

/-- Paper label: `thm:xi-time-part9xg-s10-parity-neutrality-for-s3-splitting`. -/
theorem paper_xi_time_part9xg_s10_parity_neutrality_for_s3_splitting :
    xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_statement := by
  intro D
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_sign_half_density]
  · norm_num [xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3, Fintype.card_perm]
  · norm_num [xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_s3_density,
      xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_S3, Fintype.card_perm]
  · norm_num [xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_conditional_density,
      xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_product_density,
      xi_time_part9xg_s10_parity_neutrality_for_s3_splitting_sign_half_density]

end Omega.Zeta
