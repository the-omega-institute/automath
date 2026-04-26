import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The affine frozen pressure branch recovered from the two scalar parameters. -/
def conclusion_frozen_branch_two_scalar_closure_pressure (alphaStar gStar a : ℝ) : ℝ :=
  a * alphaStar + gStar

/-- The frozen macro min-entropy is constant along the affine branch. -/
def conclusion_frozen_branch_two_scalar_closure_macroMinEntropy (gStar : ℝ) (_a : ℝ) : ℝ :=
  gStar

/-- The frozen micro min-entropy shifts the macro entropy by the max-fiber exponent. -/
def conclusion_frozen_branch_two_scalar_closure_microMinEntropy
    (alphaStar gStar : ℝ) (_a : ℝ) : ℝ :=
  alphaStar + gStar

/-- The frozen micro bitrate is the max-fiber exponent expressed in bits. -/
def conclusion_frozen_branch_two_scalar_closure_microBitrate (alphaStar : ℝ) : ℝ :=
  alphaStar / Real.log 2

/-- Closed-form recovery of the slope and intercept from two affine samples. -/
def conclusion_frozen_branch_two_scalar_closure_statement : Prop :=
  ∀ {a0 a1 alphaStar gStar : ℝ},
    a0 ≠ a1 →
    let P := conclusion_frozen_branch_two_scalar_closure_pressure alphaStar gStar
    let alphaRecovered := (P a1 - P a0) / (a1 - a0)
    let gRecovered := (a1 * P a0 - a0 * P a1) / (a1 - a0)
    alphaRecovered = alphaStar ∧
      gRecovered = gStar ∧
      (∀ a : ℝ, P a = conclusion_frozen_branch_two_scalar_closure_pressure alphaRecovered gRecovered a) ∧
      (∀ a : ℝ,
        conclusion_frozen_branch_two_scalar_closure_macroMinEntropy gRecovered a = gStar) ∧
      (∀ a : ℝ,
        conclusion_frozen_branch_two_scalar_closure_microMinEntropy alphaRecovered gRecovered a =
          alphaStar + gStar) ∧
      conclusion_frozen_branch_two_scalar_closure_microBitrate alphaRecovered =
        alphaStar / Real.log 2

/-- Paper label: `cor:conclusion-frozen-branch-two-scalar-closure`. Solving the two-point affine
system recovers the frozen slope `α_*` and intercept `g_*`, and substituting those scalars back
into the pressure, macro/micro min-entropy, and bitrate formulas closes the entire frozen branch.
-/
theorem paper_conclusion_frozen_branch_two_scalar_closure :
    conclusion_frozen_branch_two_scalar_closure_statement := by
  intro a0 a1 alphaStar gStar hne
  dsimp [conclusion_frozen_branch_two_scalar_closure_pressure]
  have hden : a1 - a0 ≠ 0 := sub_ne_zero.mpr hne.symm
  have halpha :
      (a1 * alphaStar + gStar - (a0 * alphaStar + gStar)) / (a1 - a0) = alphaStar := by
    field_simp [hden]
    ring
  have hg :
      (a1 * (a0 * alphaStar + gStar) - a0 * (a1 * alphaStar + gStar)) / (a1 - a0) = gStar := by
    field_simp [hden]
    ring_nf
  refine ⟨halpha, hg, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [halpha, hg]
  · intro a
    simpa [conclusion_frozen_branch_two_scalar_closure_macroMinEntropy] using hg
  · intro a
    rw [halpha, hg]
    simp [conclusion_frozen_branch_two_scalar_closure_microMinEntropy]
  · simpa [conclusion_frozen_branch_two_scalar_closure_microBitrate] using
      congrArg (fun x : ℝ => x / Real.log 2) halpha

end

end Omega.Conclusion
