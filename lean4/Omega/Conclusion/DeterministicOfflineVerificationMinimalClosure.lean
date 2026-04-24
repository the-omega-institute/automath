import Mathlib.Tactic
import Omega.Conclusion.CofinalSparsificationSemanticCompleteness
import Omega.Conclusion.RejectNullFiniteNormalForm
import Omega.Conclusion.ThreeEndCertificateJointSufficiencyMinimality
import Omega.Conclusion.TypedCertificateInverseLimitRigidity

namespace Omega.Conclusion

/-- Concrete null-output tags used by the deterministic offline verifier package. -/
inductive conclusion_deterministic_offline_verification_minimal_closure_null_class
  | semantic
  | protocol
  | collision
deriving DecidableEq

/-- Concrete defect-output tags used by the deterministic offline verifier package. -/
inductive conclusion_deterministic_offline_verification_minimal_closure_defect_class
  | radius
  | depth
  | endpoint
deriving DecidableEq

/-- Conclusion-level package for deterministic offline verification: inverse-limit rigidity gives
implementation-independent factorization, cofinal sparsification gives finite-level collapse, the
three-end certificate gives completeness of the advertised closure, and the finite normal-form tag
records the remaining minimal rejection mode. -/
structure conclusion_deterministic_offline_verification_minimal_closure_data where
  typed : TypedCertificateInverseLimitRigidityData
  sparsification : ConclusionCofinalSparsificationSemanticCompletenessData
  threeEnd : ThreeEndCertificateOrthogonalityData
  nullClass : conclusion_deterministic_offline_verification_minimal_closure_null_class
  defectClass : conclusion_deterministic_offline_verification_minimal_closure_defect_class

/-- Statement extracted from the deterministic offline verification package. -/
def conclusion_deterministic_offline_verification_minimal_closure_statement
    (D : conclusion_deterministic_offline_verification_minimal_closure_data) : Prop :=
  D.typed.isInverseSystem ∧
    D.typed.inverseLimitUniqueModEq ∧
    D.typed.everyCompatibleDeterministicSemanticsFactors ∧
    D.sparsification.cofinalReconstruction ∧
    D.sparsification.finiteLevelDetermination ∧
    D.threeEnd.factorsThroughProduct ∧
    D.threeEnd.failuresAreOrthogonal ∧
    (D.nullClass = .semantic ∨ D.nullClass = .protocol ∨ D.nullClass = .collision ∨
      D.defectClass = .radius ∨ D.defectClass = .depth ∨ D.defectClass = .endpoint)

/-- Paper label: `thm:conclusion-deterministic-offline-verification-minimal-closure`. -/
theorem paper_conclusion_deterministic_offline_verification_minimal_closure
    (D : conclusion_deterministic_offline_verification_minimal_closure_data) :
    conclusion_deterministic_offline_verification_minimal_closure_statement D := by
  rcases paper_conclusion_typed_certificate_inverse_limit_rigidity D.typed with
    ⟨hInverseSystem, hUnique, hFactorization⟩
  rcases paper_conclusion_cofinal_sparsification_semantic_completeness D.sparsification with
    ⟨hCofinal, hFiniteLevel⟩
  have hNull :
      D.nullClass = .semantic ∨ D.nullClass = .protocol ∨ D.nullClass = .collision := by
    cases D.nullClass <;> simp
  have hSemantic :
      D.nullClass = .semantic → ¬ D.nullClass = .protocol ∧ ¬ D.nullClass = .collision := by
    intro h
    constructor <;> intro h'
    · cases h.symm.trans h'
    · cases h.symm.trans h'
  have hProtocol :
      D.nullClass = .protocol → ¬ D.nullClass = .semantic ∧ ¬ D.nullClass = .collision := by
    intro h
    constructor <;> intro h'
    · cases h.symm.trans h'
    · cases h.symm.trans h'
  have hCollision :
      D.nullClass = .collision → ¬ D.nullClass = .semantic ∧ ¬ D.nullClass = .protocol := by
    intro h
    constructor <;> intro h'
    · cases h.symm.trans h'
    · cases h.symm.trans h'
  rcases
      paper_conclusion_three_end_certificate_joint_sufficiency_minimality D.threeEnd
        (D.nullClass = .semantic) (D.nullClass = .protocol) (D.nullClass = .collision) False
        hNull hSemantic hProtocol hCollision (by intro h; exact h) with
    ⟨hThreeEndFactors, hThreeEndOrthogonal, _hThreeEndComplete, _hNoHidden⟩
  have hDefect :
      D.defectClass = .radius ∨ D.defectClass = .depth ∨ D.defectClass = .endpoint := by
    cases D.defectClass <;> simp
  have hRadius :
      D.defectClass = .radius → ¬ D.defectClass = .depth ∧ ¬ D.defectClass = .endpoint := by
    intro h
    constructor <;> intro h'
    · cases h.symm.trans h'
    · cases h.symm.trans h'
  have hDepth :
      D.defectClass = .depth → ¬ D.defectClass = .radius ∧ ¬ D.defectClass = .endpoint := by
    intro h
    constructor <;> intro h'
    · cases h.symm.trans h'
    · cases h.symm.trans h'
  have hEndpoint :
      D.defectClass = .endpoint → ¬ D.defectClass = .radius ∧ ¬ D.defectClass = .depth := by
    intro h
    constructor <;> intro h'
    · cases h.symm.trans h'
    · cases h.symm.trans h'
  have hFiniteNormalForm :
      D.nullClass = .semantic ∨ D.nullClass = .protocol ∨ D.nullClass = .collision ∨
        D.defectClass = .radius ∨ D.defectClass = .depth ∨ D.defectClass = .endpoint := by
    exact
      paper_conclusion_reject_null_finite_normal_form
        (D.nullClass = .semantic) (D.nullClass = .protocol) (D.nullClass = .collision)
        (D.defectClass = .radius) (D.defectClass = .depth) (D.defectClass = .endpoint)
        hNull hDefect hSemantic hProtocol hCollision hRadius hDepth hEndpoint
  exact ⟨hInverseSystem, hUnique, hFactorization, hCofinal, hFiniteLevel, hThreeEndFactors,
    hThreeEndOrthogonal, hFiniteNormalForm⟩

end Omega.Conclusion
