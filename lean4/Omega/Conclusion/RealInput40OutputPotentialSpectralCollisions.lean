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

end Omega.Conclusion
