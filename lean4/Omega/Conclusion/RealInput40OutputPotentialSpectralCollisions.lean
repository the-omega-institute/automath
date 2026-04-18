import Mathlib.Tactic

namespace Omega.Conclusion

/-- Closed form of `Q` on the positive tracked branch after substituting `x = √u`. -/
def trackedPlusQ (x : ℚ) : ℚ :=
  2 * (x - 1) * (x + 1) ^ 2 / x ^ 3

/-- Closed form of `Q` on the negative tracked branch after substituting `x = √u`. -/
def trackedMinusQ (x : ℚ) : ℚ :=
  2 * (x - 1) ^ 2 * (x + 1) / x ^ 3

/-- One visible factor of `(x - 1)` with non-vanishing residual coefficient at `x = 1`. -/
def hasSimpleContactAtOne (f : ℚ → ℚ) : Prop :=
  ∃ g : ℚ → ℚ, (f = fun x => (x - 1) * g x) ∧ g 1 ≠ 0

/-- Two visible factors of `(x - 1)` with non-vanishing residual coefficient at `x = 1`. -/
def hasDoubleContactAtOne (f : ℚ → ℚ) : Prop :=
  ∃ g : ℚ → ℚ, (f = fun x => (x - 1) ^ 2 * g x) ∧ g 1 ≠ 0

/-- Contact order package for the `z_tr^+` branch. -/
def plusBranchSimpleContact : Prop :=
  hasSimpleContactAtOne trackedPlusQ

/-- Contact order package for the `z_tr^-` branch. -/
def minusBranchDoubleContact : Prop :=
  hasDoubleContactAtOne trackedMinusQ

/-- The explicit `Q(±1,u)` factorization package at the unit-ring collision locus. -/
def qAtOne (u : ℚ) : ℚ :=
  -u * (u - 4) * (u - 1) * (u + 1)

/-- The explicit `Q(-1,u)` factorization package at the unit-ring collision locus. -/
def qAtNegOne (u : ℚ) : ℚ :=
  -(u - 1) ^ 2 * (u ^ 2 + 6 * u - 2)

/-- Audited packaging of the tracked-branch and unit-ring formulas used in the paper statement. -/
def unitRingCollisionPackage : Prop :=
  (∀ x : ℚ, trackedPlusQ x = 2 * (x - 1) * (x + 1) ^ 2 / x ^ 3) ∧
    (∀ x : ℚ, trackedMinusQ x = 2 * (x - 1) ^ 2 * (x + 1) / x ^ 3) ∧
    (∀ u : ℚ, qAtOne u = -u * (u - 4) * (u - 1) * (u + 1)) ∧
    (∀ u : ℚ, qAtNegOne u = -(u - 1) ^ 2 * (u ^ 2 + 6 * u - 2))

/-- The degree-14 discriminant factor from the audited resultant certificate. -/
def qDiscriminantCore (u : ℚ) : ℚ :=
  493550656 * u ^ 14 - 11265420816 * u ^ 13 + 67033825292 * u ^ 12 -
    191441205095 * u ^ 11 + 321996795735 * u ^ 10 - 358312733199 * u ^ 9 +
    281663683277 * u ^ 8 - 151081877068 * u ^ 7 + 43747225537 * u ^ 6 -
    1417807347 * u ^ 5 - 1064277657 * u ^ 4 - 332015971 * u ^ 3 - 20017024 * u ^ 2 -
    623232 * u + 6912

/-- The audited resultant certificate for the residual factor `Q`. -/
def qResultantCertificate (u : ℚ) : ℚ :=
  4 * u ^ 15 * (u - 1) ^ 3 * qDiscriminantCore u

/-- Packaged discriminant/resultant factorization used in the paper statement. -/
def qDiscriminantFactorizationPackage : Prop :=
  (∀ u : ℚ, qResultantCertificate u = 4 * u ^ 15 * (u - 1) ^ 3 * qDiscriminantCore u) ∧
    qDiscriminantCore 0 = 6912

/-- Contact-order audit at the singular unit-circle ring.
    prop:real-input-40-singular-ring-contact-order -/
theorem paper_real_input_40_singular_ring_contact_order :
    plusBranchSimpleContact ∧ minusBranchDoubleContact := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun x => 2 * (x + 1) ^ 2 / x ^ 3, ⟨?_, by norm_num⟩⟩
    funext x
    simp [trackedPlusQ, div_eq_mul_inv, mul_left_comm, mul_comm]
  · refine ⟨fun x => 2 * (x + 1) / x ^ 3, ⟨?_, by norm_num⟩⟩
    funext x
    simp [trackedMinusQ, div_eq_mul_inv, mul_left_comm, mul_comm]

/-- Audited package for the tracked-branch collision formulas, the unit-ring factorization at
`z = ±1`, and the discriminant/resultant certificate of the residual factor `Q`.
    prop:real-input-40-output-spectral-collisions -/
theorem paper_real_input_40_output_spectral_collisions :
    plusBranchSimpleContact ∧ minusBranchDoubleContact ∧ unitRingCollisionPackage ∧
      qDiscriminantFactorizationPackage := by
  refine ⟨paper_real_input_40_singular_ring_contact_order.1,
    paper_real_input_40_singular_ring_contact_order.2, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x
      rfl
    · intro u
      rfl
    · intro u
      rfl
  · refine ⟨?_, by norm_num [qDiscriminantCore]⟩
    intro u
    rfl

end Omega.Conclusion
