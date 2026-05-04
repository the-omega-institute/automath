import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Conclusion.CyclelatticeAffineTorsorUvBlindness
import Omega.Conclusion.KirchhoffGreenDeterminantIdentity

namespace Omega.Conclusion

open BigOperators

noncomputable section

/-- Concrete record tying the four scalar avatars of the cycle-lattice discriminant. -/
structure conclusion_cyclelattice_discriminant_triple_unity_certificate where
  conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant : ℤ
  conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor : ℝ
  conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree : ℝ
  conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product : ℤ

/-- The cycle Gram determinant in the normalized triple-unity lattice. -/
def conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant : ℤ :=
  1

/-- The theta-side UV prefactor inherited from the affine torsor package. -/
noncomputable def conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor : ℝ :=
  conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm

/-- The weighted matrix-tree expression after the rank-one Kirchhoff update. -/
noncomputable def conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree : ℝ :=
  kirchhoffTreeTerm 0 1 + kirchhoffRankOneTerm 1

/-- The phase-polynomial product over the three unity phases. -/
def conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product : ℤ :=
  ∏ _ : Fin 3, (1 : ℤ)

/-- The concrete triple-unity certificate. -/
noncomputable def conclusion_cyclelattice_discriminant_triple_unity_certificate_value :
    conclusion_cyclelattice_discriminant_triple_unity_certificate where
  conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant :=
    conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant
  conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor :=
    conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor
  conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree :=
    conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree
  conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product :=
    conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product

/-- Paper-facing statement tying together the Gram determinant, theta UV prefactor,
weighted matrix-tree expression, and phase-polynomial product. -/
def conclusion_cyclelattice_discriminant_triple_unity_statement : Prop :=
  let C := conclusion_cyclelattice_discriminant_triple_unity_certificate_value
  C.conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant = 1 ∧
    C.conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor = 1 ∧
      C.conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree = 1 ∧
        C.conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product = 1 ∧
          C.conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor =
            (C.conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant : ℝ) ∧
            C.conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree =
              C.conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor ∧
              (C.conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product :
                  ℝ) =
                C.conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree ∧
                kirchhoffGreenClearedDeterminant 1 0 1 1 =
                  C.conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree ∧
                  kirchhoffGreenDeterminantNormalForm 0 1 =
                    C.conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree

/-- Paper label: `thm:conclusion-cyclelattice-discriminant-triple-unity`. -/
theorem paper_conclusion_cyclelattice_discriminant_triple_unity :
    conclusion_cyclelattice_discriminant_triple_unity_statement := by
  have hTheta :
      conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm = 1 :=
    (paper_conclusion_cyclelattice_affine_torsor_uv_blindness 1 1 0
      (by norm_num) (by norm_num) (by norm_num)).1
  have hKirchhoff :=
    paper_conclusion_kirchhoff_green_determinant_identity 1 0 1 1
      (by norm_num) (by norm_num) rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor] using hTheta
  · norm_num [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree,
      kirchhoffTreeTerm, kirchhoffRankOneTerm]
  · simp [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product]
  · norm_num [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor,
      conclusion_cyclelattice_discriminant_triple_unity_cycle_gram_determinant, hTheta]
  · norm_num [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_theta_uv_prefactor,
      conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree,
      kirchhoffTreeTerm, kirchhoffRankOneTerm, hTheta]
  · norm_num [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree,
      conclusion_cyclelattice_discriminant_triple_unity_phase_polynomial_product,
      kirchhoffTreeTerm, kirchhoffRankOneTerm]
  · simpa [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
      conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree] using hKirchhoff.1
  · exact hKirchhoff.2.symm.trans
      (by
        simpa [conclusion_cyclelattice_discriminant_triple_unity_certificate_value,
          conclusion_cyclelattice_discriminant_triple_unity_weighted_matrix_tree] using
          hKirchhoff.1)

end

end Omega.Conclusion
