import Mathlib.Tactic

namespace Omega.Conclusion

/--
Concrete obstruction data for
`thm:conclusion-finite-scalar-trigonal-reconstruction-impossible`.

The boolean fields record the three permitted operations of the scalar
trigonal reconstruction scheme.  The natural-number fields count the branch
register and Prym blind components left after these operations.
-/
structure conclusion_finite_scalar_trigonal_reconstruction_impossible_data where
  conclusion_finite_scalar_trigonal_reconstruction_impossible_usesSingleTrigonal :
    Bool
  conclusion_finite_scalar_trigonal_reconstruction_impossible_usesFiniteCubicFibers :
    Bool
  conclusion_finite_scalar_trigonal_reconstruction_impossible_readsOnlyVisibleJacobian :
    Bool
  conclusion_finite_scalar_trigonal_reconstruction_impossible_faithfulReconstruction :
    Bool
  conclusion_finite_scalar_trigonal_reconstruction_impossible_secondBranchRegister :
    ℕ
  conclusion_finite_scalar_trigonal_reconstruction_impossible_prymBlindComponent :
    ℕ
  conclusion_finite_scalar_trigonal_reconstruction_impossible_single_trigonal_loss :
    conclusion_finite_scalar_trigonal_reconstruction_impossible_usesSingleTrigonal = true →
      0 <
        conclusion_finite_scalar_trigonal_reconstruction_impossible_secondBranchRegister
  conclusion_finite_scalar_trigonal_reconstruction_impossible_finite_fiber_loss :
    conclusion_finite_scalar_trigonal_reconstruction_impossible_usesFiniteCubicFibers =
        true →
      0 <
        conclusion_finite_scalar_trigonal_reconstruction_impossible_secondBranchRegister
  conclusion_finite_scalar_trigonal_reconstruction_impossible_visible_prym_blind :
    conclusion_finite_scalar_trigonal_reconstruction_impossible_readsOnlyVisibleJacobian =
        true →
      0 <
        conclusion_finite_scalar_trigonal_reconstruction_impossible_prymBlindComponent
  conclusion_finite_scalar_trigonal_reconstruction_impossible_faithful_has_no_blind_spot :
    conclusion_finite_scalar_trigonal_reconstruction_impossible_faithfulReconstruction =
        true →
      conclusion_finite_scalar_trigonal_reconstruction_impossible_secondBranchRegister = 0 ∧
        conclusion_finite_scalar_trigonal_reconstruction_impossible_prymBlindComponent = 0

namespace conclusion_finite_scalar_trigonal_reconstruction_impossible_data

/-- The three restrictions force the faithful reconstruction flag to be false. -/
def conclusion_finite_scalar_trigonal_reconstruction_impossible_statement
    (D : conclusion_finite_scalar_trigonal_reconstruction_impossible_data) : Prop :=
  D.conclusion_finite_scalar_trigonal_reconstruction_impossible_usesSingleTrigonal =
      true →
    D.conclusion_finite_scalar_trigonal_reconstruction_impossible_usesFiniteCubicFibers =
        true →
      D.conclusion_finite_scalar_trigonal_reconstruction_impossible_readsOnlyVisibleJacobian =
          true →
        D.conclusion_finite_scalar_trigonal_reconstruction_impossible_faithfulReconstruction =
          false

end conclusion_finite_scalar_trigonal_reconstruction_impossible_data

/-- Paper label: `thm:conclusion-finite-scalar-trigonal-reconstruction-impossible`. -/
theorem paper_conclusion_finite_scalar_trigonal_reconstruction_impossible
    (D : conclusion_finite_scalar_trigonal_reconstruction_impossible_data) :
    D.conclusion_finite_scalar_trigonal_reconstruction_impossible_statement := by
  intro hsingle hfinite hvisible
  cases hfaith :
      D.conclusion_finite_scalar_trigonal_reconstruction_impossible_faithfulReconstruction
  · rfl
  · have hsingle_loss :=
      D.conclusion_finite_scalar_trigonal_reconstruction_impossible_single_trigonal_loss
        hsingle
    have hfinite_loss :=
      D.conclusion_finite_scalar_trigonal_reconstruction_impossible_finite_fiber_loss
        hfinite
    have hprym_blind :=
      D.conclusion_finite_scalar_trigonal_reconstruction_impossible_visible_prym_blind
        hvisible
    rcases
      D.conclusion_finite_scalar_trigonal_reconstruction_impossible_faithful_has_no_blind_spot
        hfaith with
      ⟨hbranch_zero, hprym_zero⟩
    omega

end Omega.Conclusion
