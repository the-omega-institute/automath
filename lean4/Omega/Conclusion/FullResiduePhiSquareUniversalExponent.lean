import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FullResidueRegularSimplexOrbit
import Omega.Conclusion.MinimalAnomalyBlockRelativeRankPhiSquareInverse

open scoped BigOperators

namespace Omega.Conclusion

open Filter
open scoped Topology

noncomputable section

/-- Concrete data for the full-residue `φ^{-2}` exponent package.  The even branch is the
regular-simplex finite residue orbit; the odd branch is supplied by the atom-dominated profile;
the universal exponent is transported through the existing anomaly-block ratio theorem. -/
structure conclusion_full_residue_phi_square_universal_exponent_data where
  conclusion_full_residue_phi_square_universal_exponent_m : ℕ
  conclusion_full_residue_phi_square_universal_exponent_m_pos :
    0 < conclusion_full_residue_phi_square_universal_exponent_m
  conclusion_full_residue_phi_square_universal_exponent_oddDeviation : ℕ → ℝ
  conclusion_full_residue_phi_square_universal_exponent_rhoCore : ℝ
  conclusion_full_residue_phi_square_universal_exponent_minBlockDim : ℕ → ℕ
  conclusion_full_residue_phi_square_universal_exponent_abDim : ℕ → ℕ
  conclusion_full_residue_phi_square_universal_exponent_minCount : ℕ → ℕ
  conclusion_full_residue_phi_square_universal_exponent_totalCount : ℕ → ℕ
  conclusion_full_residue_phi_square_universal_exponent_oddLimit :
    Tendsto conclusion_full_residue_phi_square_universal_exponent_oddDeviation atTop
      (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2))
  conclusion_full_residue_phi_square_universal_exponent_rhoCore_lt_one :
    conclusion_full_residue_phi_square_universal_exponent_rhoCore < 1
  conclusion_full_residue_phi_square_universal_exponent_minBlockDim_eq :
    ∀ n,
      conclusion_full_residue_phi_square_universal_exponent_minBlockDim n =
        conclusion_full_residue_phi_square_universal_exponent_minCount n
  conclusion_full_residue_phi_square_universal_exponent_abDim_eq :
    ∀ n,
      conclusion_full_residue_phi_square_universal_exponent_abDim n =
        conclusion_full_residue_phi_square_universal_exponent_totalCount n
  conclusion_full_residue_phi_square_universal_exponent_countLimit :
    Tendsto
      (fun n =>
        (conclusion_full_residue_phi_square_universal_exponent_minCount n : ℝ) /
          conclusion_full_residue_phi_square_universal_exponent_totalCount n)
      atTop
      (nhds (Real.goldenRatio ^ (-2 : ℤ)))

namespace conclusion_full_residue_phi_square_universal_exponent_data

/-- The even-length residue deviations are the regular-simplex squared norms. -/
def evenDeviationLimit (D : conclusion_full_residue_phi_square_universal_exponent_data) :
    Prop :=
  ∀ r : Fin D.conclusion_full_residue_phi_square_universal_exponent_m,
    (∑ i : Fin D.conclusion_full_residue_phi_square_universal_exponent_m,
      (((if i = r then 1 else 0 : ℚ) -
        (1 / (D.conclusion_full_residue_phi_square_universal_exponent_m : ℚ))) ^ 2)) =
      ((D.conclusion_full_residue_phi_square_universal_exponent_m : ℚ) - 1) /
        (D.conclusion_full_residue_phi_square_universal_exponent_m : ℚ)

/-- The atom-dominated odd profile has the golden inverse-square limit. -/
def oddDeviationLimit (D : conclusion_full_residue_phi_square_universal_exponent_data) :
    Prop :=
  Tendsto D.conclusion_full_residue_phi_square_universal_exponent_oddDeviation atTop
    (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2))

/-- In the subunit core-radius regime, the anomaly-block/full-residue ratio has exponent
`φ^{-2}`. -/
def universalExponent (D : conclusion_full_residue_phi_square_universal_exponent_data) :
    Prop :=
  D.conclusion_full_residue_phi_square_universal_exponent_rhoCore < 1 ∧
    Tendsto
      (fun n =>
        (D.conclusion_full_residue_phi_square_universal_exponent_minBlockDim n : ℝ) /
          D.conclusion_full_residue_phi_square_universal_exponent_abDim n)
      atTop
      (nhds (Real.goldenRatio ^ (-2 : ℤ)))

end conclusion_full_residue_phi_square_universal_exponent_data

/-- Paper label: `cor:conclusion-full-residue-phi-square-universal-exponent`. -/
theorem paper_conclusion_full_residue_phi_square_universal_exponent
    (D : conclusion_full_residue_phi_square_universal_exponent_data) :
    D.evenDeviationLimit ∧ D.oddDeviationLimit ∧ D.universalExponent := by
  have heven :=
    paper_conclusion_full_residue_regular_simplex_orbit
      D.conclusion_full_residue_phi_square_universal_exponent_m
      D.conclusion_full_residue_phi_square_universal_exponent_m_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heven.2.1
  · exact D.conclusion_full_residue_phi_square_universal_exponent_oddLimit
  · exact D.conclusion_full_residue_phi_square_universal_exponent_rhoCore_lt_one
  · exact paper_conclusion_minimal_anomaly_block_relative_rank_phi_square_inverse
      Real.goldenRatio
      D.conclusion_full_residue_phi_square_universal_exponent_minBlockDim
      D.conclusion_full_residue_phi_square_universal_exponent_abDim
      D.conclusion_full_residue_phi_square_universal_exponent_minCount
      D.conclusion_full_residue_phi_square_universal_exponent_totalCount
      D.conclusion_full_residue_phi_square_universal_exponent_minBlockDim_eq
      D.conclusion_full_residue_phi_square_universal_exponent_abDim_eq
      D.conclusion_full_residue_phi_square_universal_exponent_countLimit

end

end Omega.Conclusion
