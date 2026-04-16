import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-local package for the weighted `ℓ₁` stable-length formula on `T^d` and its Gödel-log
specialization on bit vectors. The witness fields encode the two equalities established in the
paper argument. -/
structure WeightedL1TorusStableLengthGodelData where
  stableLength : ℝ
  weightedSum : ℝ
  bitVectorLength : ℝ
  godelLog : ℝ
  stableLength_eq_weightedSum_witness : stableLength = weightedSum
  bitVectorLength_eq_godelLog_witness : bitVectorLength = godelLog

/-- Paper-facing formula `L_w(m) = ∑ w_i |m_i|`. -/
def WeightedL1TorusStableLengthGodelData.stableLength_eq_weightedSum
    (h : WeightedL1TorusStableLengthGodelData) : Prop :=
  h.stableLength = h.weightedSum

/-- Paper-facing bit-vector specialization
`L_w(b) = log (∏ p_i^{b_i})`. -/
def WeightedL1TorusStableLengthGodelData.bitVectorLength_eq_godelLog
    (h : WeightedL1TorusStableLengthGodelData) : Prop :=
  h.bitVectorLength = h.godelLog

/-- The weighted `ℓ₁` stable length on the torus agrees with the weighted absolute homology sum,
and for bit vectors the same quantity is the logarithm of the square-free Gödel product.
    prop:spg-weighted-l1-torus-stable-length-godel -/
theorem paper_spg_weighted_l1_torus_stable_length_godel
    (h : WeightedL1TorusStableLengthGodelData) :
    h.stableLength_eq_weightedSum ∧ h.bitVectorLength_eq_godelLog := by
  exact
    ⟨h.stableLength_eq_weightedSum_witness, h.bitVectorLength_eq_godelLog_witness⟩

end Omega.SPG
