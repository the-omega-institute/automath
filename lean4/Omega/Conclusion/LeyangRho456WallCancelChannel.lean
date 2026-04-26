import Mathlib.Tactic

namespace Omega.Conclusion

/-- The `rho_4`, `rho_5`, `rho_6` wall-cancel channel.
    cor:conclusion-leyang-rho456-wall-cancel-channel -/
noncomputable def conclusion_leyang_rho456_wall_cancel_channel_linear
    (F4 F5 F6 : ℝ) : ℝ :=
  F4 - (25 / 12) * F5 + F6

/-- The fourth cyclotomic factor used after cancellation. -/
noncomputable def conclusion_leyang_rho456_wall_cancel_channel_phi4 (u : ℝ) : ℝ :=
  u ^ 2 + 1

/-- The product of the third and sixth cyclotomic factors used after cancellation. -/
noncomputable def conclusion_leyang_rho456_wall_cancel_channel_phi3_mul_phi6 (u : ℝ) : ℝ :=
  u ^ 4 + u ^ 2 + 1

/-- Concrete coefficient and cyclotomic identities for the rho456 wall-cancel channel. -/
def conclusion_leyang_rho456_wall_cancel_channel_statement : Prop :=
  (∀ F4 F5 F6 L4 L6 : ℝ,
    F4 - (5 / 4) * F5 = -(1 / 24) * L6 →
      F6 - (5 / 6) * F5 = (1 / 24) * L4 →
        conclusion_leyang_rho456_wall_cancel_channel_linear F4 F5 F6 =
          (1 / 24) * (L4 - L6)) ∧
  (∀ u : ℝ,
    (u ^ 4 - 1) * conclusion_leyang_rho456_wall_cancel_channel_phi3_mul_phi6 u =
      (u ^ 6 - 1) * conclusion_leyang_rho456_wall_cancel_channel_phi4 u) ∧
  (∀ u : ℝ,
    conclusion_leyang_rho456_wall_cancel_channel_phi4 u /
        conclusion_leyang_rho456_wall_cancel_channel_phi3_mul_phi6 u =
      (u ^ 2 + 1) / (u ^ 4 + u ^ 2 + 1))

/-- Paper label: `cor:conclusion-leyang-rho456-wall-cancel-channel`.
The channel coefficients add the rho4 and rho6 wall identities with the common rho5 coefficient
`-25/12`, and the residual cyclotomic factor is `(u^2 + 1)/(u^4 + u^2 + 1)`. -/
theorem paper_conclusion_leyang_rho456_wall_cancel_channel :
    conclusion_leyang_rho456_wall_cancel_channel_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro F4 F5 F6 L4 L6 h46 h65
    unfold conclusion_leyang_rho456_wall_cancel_channel_linear
    nlinarith
  · intro u
    unfold conclusion_leyang_rho456_wall_cancel_channel_phi3_mul_phi6
      conclusion_leyang_rho456_wall_cancel_channel_phi4
    ring
  · intro u
    rfl

end Omega.Conclusion
