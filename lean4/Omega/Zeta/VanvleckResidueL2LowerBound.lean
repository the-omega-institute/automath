import Mathlib.Tactic

namespace Omega.Zeta

/-- The `L²` energy of the two Van Vleck residues written in real and imaginary coordinates. -/
def xiVanvleckResidueL2Energy (x₁ y₁ x₂ y₂ : ℝ) : ℝ :=
  x₁ ^ 2 + y₁ ^ 2 + x₂ ^ 2 + y₂ ^ 2

/-- The sharp lower bound forced by the total real and imaginary residue sums. -/
noncomputable def xiVanvleckResidueL2LowerBound (S Q : ℝ) : ℝ :=
  S ^ 2 / 2 + Q ^ 2 / 2

private lemma xiVanvleckResidueL2Energy_decomposition
    (x₁ y₁ x₂ y₂ S Q : ℝ) (hS : x₁ + x₂ = S) (hQ : y₁ + y₂ = Q) :
    xiVanvleckResidueL2Energy x₁ y₁ x₂ y₂ =
      xiVanvleckResidueL2LowerBound S Q + (x₁ - x₂) ^ 2 / 2 + (y₁ - y₂) ^ 2 / 2 := by
  rw [← hS, ← hQ]
  unfold xiVanvleckResidueL2Energy xiVanvleckResidueL2LowerBound
  ring

/-- The residue `L²` norm is minimized when both residues are equal to the average constrained by
the total real part `S` and total imaginary part `Q`. Equivalently, under the two linear
constraints the quadratic energy is bounded below by `(S² + Q²) / 2`, with equality exactly at the
unique stationary point.
    thm:xi-vanvleck-residue-l2-lower-bound -/
theorem paper_xi_vanvleck_residue_l2_lower_bound
    (x₁ y₁ x₂ y₂ S Q : ℝ) (hS : x₁ + x₂ = S) (hQ : y₁ + y₂ = Q) :
    xiVanvleckResidueL2LowerBound S Q ≤ xiVanvleckResidueL2Energy x₁ y₁ x₂ y₂ ∧
      (xiVanvleckResidueL2Energy x₁ y₁ x₂ y₂ = xiVanvleckResidueL2LowerBound S Q ↔
        x₁ = S / 2 ∧ y₁ = Q / 2 ∧ x₂ = S / 2 ∧ y₂ = Q / 2) := by
  have hdecomp := xiVanvleckResidueL2Energy_decomposition x₁ y₁ x₂ y₂ S Q hS hQ
  refine ⟨?_, ?_⟩
  · have hnonnegx : 0 ≤ (x₁ - x₂) ^ 2 / 2 := by positivity
    have hnonnegy : 0 ≤ (y₁ - y₂) ^ 2 / 2 := by positivity
    nlinarith [hdecomp, hnonnegx, hnonnegy]
  · constructor
    · intro heq
      have hxzero : (x₁ - x₂) ^ 2 = 0 := by
        nlinarith [hdecomp, heq, sq_nonneg (x₁ - x₂), sq_nonneg (y₁ - y₂)]
      have hyzero : (y₁ - y₂) ^ 2 = 0 := by
        nlinarith [hdecomp, heq, sq_nonneg (x₁ - x₂), sq_nonneg (y₁ - y₂)]
      have hxeq : x₁ = x₂ := by nlinarith
      have hyeq : y₁ = y₂ := by nlinarith
      have hxavg : x₁ = S / 2 := by nlinarith [hS, hxeq]
      have hyavg : y₁ = Q / 2 := by nlinarith [hQ, hyeq]
      refine ⟨hxavg, hyavg, ?_, ?_⟩ <;> nlinarith
    · rintro ⟨hx₁, hy₁, hx₂, hy₂⟩
      subst x₁ y₁ x₂ y₂
      unfold xiVanvleckResidueL2Energy xiVanvleckResidueL2LowerBound
      ring

end Omega.Zeta
