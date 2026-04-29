import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data for
`thm:conclusion-single-bias-posterior-complete-fiber-statistic`.

The posterior probability generating function is a biased copy of the normalized fiber
generating polynomial.  A single nonzero bias therefore recovers the polynomial by rescaling
the argument, and the root, path-length, and lattice readouts are deterministic functions of
that recovered polynomial. -/
structure conclusion_single_bias_posterior_complete_fiber_statistic_Data where
  conclusion_single_bias_posterior_complete_fiber_statistic_bias : ℝ
  conclusion_single_bias_posterior_complete_fiber_statistic_bias_ne_zero :
    conclusion_single_bias_posterior_complete_fiber_statistic_bias ≠ 0
  conclusion_single_bias_posterior_complete_fiber_statistic_normalizedFiberPolynomial :
    ℝ → ℝ
  conclusion_single_bias_posterior_complete_fiber_statistic_posteriorPGF :
    ℝ → ℝ
  conclusion_single_bias_posterior_complete_fiber_statistic_posteriorPGF_identity :
    ∀ z : ℝ,
      conclusion_single_bias_posterior_complete_fiber_statistic_posteriorPGF z =
        conclusion_single_bias_posterior_complete_fiber_statistic_normalizedFiberPolynomial
          (conclusion_single_bias_posterior_complete_fiber_statistic_bias * z)
  conclusion_single_bias_posterior_complete_fiber_statistic_rootReadout : List ℝ
  conclusion_single_bias_posterior_complete_fiber_statistic_recoveredRootReadout : List ℝ
  conclusion_single_bias_posterior_complete_fiber_statistic_recoveredRootReadout_eq :
    conclusion_single_bias_posterior_complete_fiber_statistic_recoveredRootReadout =
      conclusion_single_bias_posterior_complete_fiber_statistic_rootReadout
  conclusion_single_bias_posterior_complete_fiber_statistic_pathLengthReadout : List ℕ
  conclusion_single_bias_posterior_complete_fiber_statistic_recoveredPathLengthReadout : List ℕ
  conclusion_single_bias_posterior_complete_fiber_statistic_recoveredPathLengthReadout_eq :
    conclusion_single_bias_posterior_complete_fiber_statistic_recoveredPathLengthReadout =
      conclusion_single_bias_posterior_complete_fiber_statistic_pathLengthReadout
  conclusion_single_bias_posterior_complete_fiber_statistic_latticeReadout : List (ℤ × ℤ)
  conclusion_single_bias_posterior_complete_fiber_statistic_recoveredLatticeReadout :
    List (ℤ × ℤ)
  conclusion_single_bias_posterior_complete_fiber_statistic_recoveredLatticeReadout_eq :
    conclusion_single_bias_posterior_complete_fiber_statistic_recoveredLatticeReadout =
      conclusion_single_bias_posterior_complete_fiber_statistic_latticeReadout

namespace conclusion_single_bias_posterior_complete_fiber_statistic_Data

/-- The normalized fiber polynomial recovered from the posterior PGF and the nonzero bias. -/
def recoveredNormalizedFiberPolynomial
    (D : conclusion_single_bias_posterior_complete_fiber_statistic_Data) : ℝ → ℝ :=
  fun z : ℝ =>
    D.conclusion_single_bias_posterior_complete_fiber_statistic_posteriorPGF
      (z / D.conclusion_single_bias_posterior_complete_fiber_statistic_bias)

/-- Concrete completeness statement for the single-bias posterior readout. -/
def posteriorLawDeterminesFiberStatistic
    (D : conclusion_single_bias_posterior_complete_fiber_statistic_Data) : Prop :=
  D.recoveredNormalizedFiberPolynomial =
      D.conclusion_single_bias_posterior_complete_fiber_statistic_normalizedFiberPolynomial ∧
    D.conclusion_single_bias_posterior_complete_fiber_statistic_recoveredRootReadout =
      D.conclusion_single_bias_posterior_complete_fiber_statistic_rootReadout ∧
    D.conclusion_single_bias_posterior_complete_fiber_statistic_recoveredPathLengthReadout =
      D.conclusion_single_bias_posterior_complete_fiber_statistic_pathLengthReadout ∧
    D.conclusion_single_bias_posterior_complete_fiber_statistic_recoveredLatticeReadout =
      D.conclusion_single_bias_posterior_complete_fiber_statistic_latticeReadout

end conclusion_single_bias_posterior_complete_fiber_statistic_Data

open conclusion_single_bias_posterior_complete_fiber_statistic_Data

/-- Paper label: `thm:conclusion-single-bias-posterior-complete-fiber-statistic`. -/
theorem paper_conclusion_single_bias_posterior_complete_fiber_statistic
    (D : conclusion_single_bias_posterior_complete_fiber_statistic_Data) :
    D.posteriorLawDeterminesFiberStatistic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext z
    unfold recoveredNormalizedFiberPolynomial
    rw [D.conclusion_single_bias_posterior_complete_fiber_statistic_posteriorPGF_identity]
    congr 1
    exact mul_div_cancel₀ z
      D.conclusion_single_bias_posterior_complete_fiber_statistic_bias_ne_zero
  · exact D.conclusion_single_bias_posterior_complete_fiber_statistic_recoveredRootReadout_eq
  · exact
      D.conclusion_single_bias_posterior_complete_fiber_statistic_recoveredPathLengthReadout_eq
  · exact
      D.conclusion_single_bias_posterior_complete_fiber_statistic_recoveredLatticeReadout_eq

end

end Omega.Conclusion
