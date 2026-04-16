import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local witness for the determinant-ratio identity. The partial derivative data are
recorded only along the branch `z = zStar u`, together with the differentiated root equation and a
resultant eliminating `z`. -/
structure BetaDeterminantRatioWitness where
  Delta : ℝ → ℝ → ℝ
  zStar : ℝ → ℝ
  beta : ℝ → ℝ
  dDeltaDz : ℝ → ℝ
  dDeltaDu : ℝ → ℝ
  zStarDeriv : ℝ → ℝ
  rootEquation : ∀ u, Delta (zStar u) u = 0
  differentiatedRootEquation : ∀ u, dDeltaDz u * zStarDeriv u + dDeltaDu u = 0
  simpleRoot : ∀ u, dDeltaDz u ≠ 0
  zStar_ne_zero : ∀ u, zStar u ≠ 0
  betaLogDerivative : ∀ u, beta u = -(u * zStarDeriv u) / zStar u
  resultant : ℝ → ℝ → ℤ
  resultant_spec : ∀ u, resultant (beta u) u = 0

/-- The paper-facing derivative ratio identity obtained by differentiating
`Delta (zStar u) u = 0` and solving for `zStar'`. -/
def BetaDeterminantRatioWitness.derivativeRatioIdentity (h : BetaDeterminantRatioWitness) : Prop :=
  ∀ u,
    h.beta u =
      (u / h.zStar u) * (h.dDeltaDu u / h.dDeltaDz u)

/-- The paper-facing elimination clause: after clearing denominators, `(beta(u), u)` is annihilated
by the resultant in the eliminated `z` variable. -/
def BetaDeterminantRatioWitness.resultantElimination (h : BetaDeterminantRatioWitness) : Prop :=
  ∀ u, h.resultant (h.beta u) u = 0

set_option maxHeartbeats 400000 in
/-- Paper wrapper for the determinant-ratio package. The first clause is the logarithmic
derivative identity for `beta`, and the second packages the same witness data as a resultant
elimination statement.
    prop:gut-beta-determinant-ratio -/
theorem paper_gut_beta_determinant_ratio (h : BetaDeterminantRatioWitness) :
    h.derivativeRatioIdentity ∧ h.resultantElimination := by
  refine ⟨?_, ?_⟩
  · intro u
    have hd : h.dDeltaDz u ≠ 0 := h.simpleRoot u
    have hz : h.zStar u ≠ 0 := h.zStar_ne_zero u
    have hzstar :
        h.zStarDeriv u = -h.dDeltaDu u / h.dDeltaDz u := by
      apply (eq_div_iff hd).2
      nlinarith [h.differentiatedRootEquation u]
    calc
      h.beta u = -(u * h.zStarDeriv u) / h.zStar u := h.betaLogDerivative u
      _ = -(u * (-h.dDeltaDu u / h.dDeltaDz u)) / h.zStar u := by rw [hzstar]
      _ = (u / h.zStar u) * (h.dDeltaDu u / h.dDeltaDz u) := by
        field_simp [hd, hz]
  · intro u
    exact h.resultant_spec u

end Omega.GU
