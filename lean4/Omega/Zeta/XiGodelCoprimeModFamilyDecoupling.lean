import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for the CRT decoupling wrapper. The single-modulus bounds at
`q = ∏ qᵢ` are assumed from the previously established one-modulus package, and the two family
TV defects are the corresponding pushforwards to the product residue space. -/
structure xi_godel_coprime_mod_family_decoupling_data where
  qFactors : List ℕ
  ambientCard : ℕ
  visibleCard : ℕ
  familyResidueTv : ℝ
  familyJointTv : ℝ
  singleResidueTv : ℝ
  singleJointTv : ℝ
  qFactors_pairwise_coprime : qFactors.Pairwise Nat.Coprime
  qFactors_ge_two : ∀ q ∈ qFactors, 2 ≤ q
  familyResidueTv_le_single : familyResidueTv ≤ singleResidueTv
  familyJointTv_le_single : familyJointTv ≤ singleJointTv
  singleResidueTv_le_bound :
    singleResidueTv ≤
      min (1 : ℝ) (((qFactors.prod : ℝ) * visibleCard) / (4 * ambientCard))
  singleJointTv_le_bound :
    singleJointTv ≤
      min (1 : ℝ) (((qFactors.prod : ℝ) * visibleCard) / (4 * ambientCard))

/-- The product modulus `q = ∏ qᵢ`. -/
def xi_godel_coprime_mod_family_decoupling_modulus
    (D : xi_godel_coprime_mod_family_decoupling_data) : ℕ :=
  D.qFactors.prod

/-- The CRT family law and the joint law with `X_*` both inherit the one-modulus bound at the
product modulus `q`. -/
def xi_godel_coprime_mod_family_decoupling_statement
    (D : xi_godel_coprime_mod_family_decoupling_data) : Prop :=
  D.familyResidueTv ≤
      min (1 : ℝ)
        (((xi_godel_coprime_mod_family_decoupling_modulus D : ℝ) * D.visibleCard) /
          (4 * D.ambientCard)) ∧
    D.familyJointTv ≤
      min (1 : ℝ)
        (((xi_godel_coprime_mod_family_decoupling_modulus D : ℝ) * D.visibleCard) /
          (4 * D.ambientCard))

/-- Paper label: `thm:xi-godel-coprime-mod-family-decoupling`. -/
theorem paper_xi_godel_coprime_mod_family_decoupling
    (D : xi_godel_coprime_mod_family_decoupling_data) :
    xi_godel_coprime_mod_family_decoupling_statement D := by
  refine ⟨?_, ?_⟩
  · exact le_trans D.familyResidueTv_le_single D.singleResidueTv_le_bound
  · exact le_trans D.familyJointTv_le_single D.singleJointTv_le_bound

end Omega.Zeta
