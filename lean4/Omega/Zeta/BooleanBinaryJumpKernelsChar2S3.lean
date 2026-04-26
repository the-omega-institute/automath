import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-boolean-binary-jump-kernels-char2-s3`. Once the order-three identity,
inverse relation, `S_3` conjugacy, and spectral package are available, the paper statement is just
their conjunction. -/
theorem paper_xi_boolean_binary_jump_kernels_char2_s3
    (orderThree inverseRelation s3Conjugacy spectralDecomposition : Prop) :
    orderThree →
      inverseRelation →
      s3Conjugacy →
      spectralDecomposition →
      (orderThree ∧ inverseRelation ∧ s3Conjugacy ∧ spectralDecomposition) := by
  intro hOrder hInv hS3 hSpec
  exact ⟨hOrder, hInv, hS3, hSpec⟩

end Omega.Zeta
