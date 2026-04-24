import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.TwoAtomScalarRecoveryAlpha2
import Omega.Zeta.XiTimePart9odEscortEscortFdivBinaryClosure
import Omega.Zeta.XiTimePart9odEscortTvCollapseBlockUniform

namespace Omega.Conclusion

open Omega.Zeta

noncomputable section

/-- Concrete datum recording the two escort temperatures whose binary collapse is being packaged. -/
structure BinfoldEscortCsiszarBlackwellPhiDatum where
  p : ℕ
  q : ℕ

namespace BinfoldEscortCsiszarBlackwellPhiDatum

/-- Pearson `χ²` specialization of the binary escort `f`-divergence. -/
noncomputable def chi2Limit (D : BinfoldEscortCsiszarBlackwellPhiDatum) : ℝ :=
  xiEscortBinaryFDivLimit (fun u => (u - 1) ^ 2) D.p D.q

/-- The `χ²`-type scalar at the reference pair `(0,1)`, used to recover `φ`. -/
noncomputable def chi2UniformBaseline : ℝ :=
  twoAtomScalar2 Real.goldenRatio

/-- Publication-facing package: the full binary `f`-divergence collapse, its TV and `χ²`
sections, and the affine recovery of the golden ratio from the baseline `χ²` scalar. -/
def Holds (D : BinfoldEscortCsiszarBlackwellPhiDatum) : Prop :=
  (∀ f : ℝ → ℝ,
    xiEscortBinaryFDivLimit f D.p D.q =
      (1 - xiEscortTheta D.p) * f ((1 - xiEscortTheta D.q) / (1 - xiEscortTheta D.p)) +
        xiEscortTheta D.p * f (xiEscortTheta D.q / xiEscortTheta D.p)) ∧
    xiEscortTvDistance (xiEscortBinaryLaw D.p) (xiEscortBinaryLaw D.q) =
      |xiEscortTheta D.q - xiEscortTheta D.p| ∧
    D.chi2Limit =
      (xiEscortTheta D.q - xiEscortTheta D.p) ^ 2 /
        (xiEscortTheta D.p * (1 - xiEscortTheta D.p)) ∧
    chi2UniformBaseline = (2 * Real.goldenRatio - 3) / 5 ∧
    Real.goldenRatio = (5 * chi2UniformBaseline + 3) / 2

end BinfoldEscortCsiszarBlackwellPhiDatum

open BinfoldEscortCsiszarBlackwellPhiDatum

private theorem xiEscortBinaryChi2_closed (p q : ℕ) :
    xiEscortBinaryFDivLimit (fun u => (u - 1) ^ 2) p q =
      (xiEscortTheta q - xiEscortTheta p) ^ 2 /
        (xiEscortTheta p * (1 - xiEscortTheta p)) := by
  rw [paper_xi_time_part9od_escort_escort_fdiv_binary_closure]
  set θp := xiEscortTheta p
  set θq := xiEscortTheta q
  have hθp : 0 < θp := by
    simpa [θp] using xiEscortTheta_pos p
  have h1θp : 0 < 1 - θp := by
    simpa [θp] using xiEscortTheta_one_sub_pos p
  field_simp [hθp.ne', h1θp.ne']
  ring

private theorem binfoldEscortChi2UniformBaseline_closed :
    BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline =
      (2 * Real.goldenRatio - 3) / 5 := by
  rw [BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline, twoAtomScalar2_goldenRatio]
  nlinarith [Real.goldenRatio_sq]

private theorem goldenRatio_from_binfoldEscortChi2UniformBaseline :
    Real.goldenRatio =
      (5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 3) / 2 := by
  rw [binfoldEscortChi2UniformBaseline_closed]
  nlinarith

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:conclusion-binfold-escort-csiszar-blackwell-phi`. The general binary
`f`-divergence collapse specializes to TV and Pearson `χ²`, and the baseline `χ²` scalar recovers
the golden ratio by an explicit affine formula. -/
theorem paper_conclusion_binfold_escort_csiszar_blackwell_phi
    (D : BinfoldEscortCsiszarBlackwellPhiDatum) : D.Holds := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact paper_xi_time_part9od_escort_escort_fdiv_binary_closure f D.p D.q
  · simpa [xiEscortBinaryLaw, abs_sub_comm] using
      xiEscortTvDistance_blockLaw (xiEscortTheta D.p) (xiEscortTheta D.q)
  · simpa [BinfoldEscortCsiszarBlackwellPhiDatum.chi2Limit] using
      xiEscortBinaryChi2_closed D.p D.q
  · exact binfoldEscortChi2UniformBaseline_closed
  · exact goldenRatio_from_binfoldEscortChi2UniformBaseline

end

end Omega.Conclusion
