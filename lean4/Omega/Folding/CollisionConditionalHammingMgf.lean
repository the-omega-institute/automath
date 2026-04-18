import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

noncomputable section

/-- The four binary words of length `2`, used as a concrete seed model for the conditional
Hamming-MGF identity. -/
def twoBitWords : Finset (Bool × Bool) :=
  ({false, true} : Finset Bool).product ({false, true} : Finset Bool)

/-- Hamming distance on the seed two-bit model. -/
def seedHammingDist (ω η : Bool × Bool) : Nat :=
  (if ω.1 = η.1 then 0 else 1) + (if ω.2 = η.2 then 0 else 1)

/-- Seed collision event: the two words have the same parity, equivalently an even Hamming
distance. -/
def seedCollision (ω η : Bool × Bool) : Prop :=
  seedHammingDist ω η % 2 = 0

instance instDecidableSeedCollision (ω η : Bool × Bool) : Decidable (seedCollision ω η) := by
  unfold seedCollision seedHammingDist
  infer_instance

/-- Unconditional collision-weighted Hamming generating function on the two-bit seed. -/
def seedCollisionHammingMgf (u : ℝ) : ℝ :=
  (1 / 16 : ℝ) *
    Finset.sum (twoBitWords.product twoBitWords) (fun p =>
      if seedCollision p.1 p.2 then u ^ seedHammingDist p.1 p.2 else 0
    )

/-- Root-of-unity / coordinate-factorized closed form for the two-bit seed. -/
def seedRootUnityClosedForm (u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (((1 + u) / 2) ^ (2 : ℕ) + ((1 - u) / 2) ^ (2 : ℕ))

/-- Collision probability of the two-bit seed. -/
def seedCollisionProbability : ℝ :=
  seedCollisionHammingMgf 1

/-- Conditional Hamming generating function on the collision event. -/
def seedConditionalMgf (u : ℝ) : ℝ :=
  seedCollisionHammingMgf u / seedCollisionProbability

/-- Subset-energy expansion for the two-bit seed: only the empty subset and the full subset
survive in the even-parity collision filter. -/
def seedSubsetEnergyExpansion (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) + (1 / 4 : ℝ) * u ^ (2 : ℕ)

private theorem twoBitPairs_enum :
    twoBitWords.product twoBitWords =
      { ((false, false), (false, false)),
        ((false, false), (false, true)),
        ((false, false), (true, false)),
        ((false, false), (true, true)),
        ((false, true), (false, false)),
        ((false, true), (false, true)),
        ((false, true), (true, false)),
        ((false, true), (true, true)),
        ((true, false), (false, false)),
        ((true, false), (false, true)),
        ((true, false), (true, false)),
        ((true, false), (true, true)),
        ((true, true), (false, false)),
        ((true, true), (false, true)),
        ((true, true), (true, false)),
        ((true, true), (true, true)) } := by
  native_decide

private theorem twoBitCollisionPair_count :
    ((twoBitWords.product twoBitWords).filter (fun p => seedCollision p.1 p.2)).card = 8 := by
  native_decide

/-- Two-bit parity-collision seed for the conditional Hamming MGF:
the collision-weighted generating function agrees with the root-of-unity closed form, the
collision probability is `1/2`, the conditional MGF is `(1 + u²) / 2`, and the same expression
admits the subset-energy polynomial expansion.
    prop:fold-collision-conditional-hamming-mgf -/
theorem paper_fold_collision_conditional_hamming_mgf (u : ℝ) :
    seedCollisionHammingMgf u = seedRootUnityClosedForm u ∧
      seedCollisionProbability = (1 / 2 : ℝ) ∧
      seedConditionalMgf u = (1 + u ^ (2 : ℕ)) / 2 ∧
      seedRootUnityClosedForm u = seedSubsetEnergyExpansion u := by
  have hmgf : seedCollisionHammingMgf u = (1 + u ^ (2 : ℕ)) / 4 := by
    rw [seedCollisionHammingMgf, twoBitPairs_enum]
    simp [seedCollision, seedHammingDist]
    ring
  have hroot : seedRootUnityClosedForm u = (1 + u ^ (2 : ℕ)) / 4 := by
    unfold seedRootUnityClosedForm
    ring_nf
  have hprob : seedCollisionProbability = (1 / 2 : ℝ) := by
    unfold seedCollisionProbability seedCollisionHammingMgf
    simp
    have hcountNat : {x ∈ twoBitWords ×ˢ twoBitWords | seedCollision x.1 x.2}.card = 8 := by
      simpa using twoBitCollisionPair_count
    have hcount : (({x ∈ twoBitWords ×ˢ twoBitWords | seedCollision x.1 x.2}.card : ℕ) : ℝ) = 8 := by
      exact_mod_cast hcountNat
    rw [hcount]
    norm_num
  have hsubset : seedSubsetEnergyExpansion u = (1 + u ^ (2 : ℕ)) / 4 := by
    unfold seedSubsetEnergyExpansion
    norm_num
    ring
  refine ⟨hmgf.trans hroot.symm, hprob, ?_, ?_⟩
  · unfold seedConditionalMgf
    rw [hmgf, hprob]
    field_simp
    ring
  · exact hroot.trans hsubset.symm

/-- First-coordinate mismatch indicator on the two-bit seed. -/
def seedFirstCoordinateMismatch (p : (Bool × Bool) × (Bool × Bool)) : ℝ :=
  if p.1.1 = p.2.1 then 0 else 1

/-- Second-coordinate mismatch indicator on the two-bit seed. -/
def seedSecondCoordinateMismatch (p : (Bool × Bool) × (Bool × Bool)) : ℝ :=
  if p.1.2 = p.2.2 then 0 else 1

/-- Conditional expectation over the parity-collision event for the uniform two-bit seed. -/
def seedConditionalExpectation (f : (Bool × Bool) × (Bool × Bool) → ℝ) : ℝ :=
  (1 / 8 : ℝ) *
    Finset.sum (twoBitWords.product twoBitWords) (fun p => if seedCollision p.1 p.2 then f p else 0)

/-- Conditional first moment of the first mismatch coordinate. -/
def seedConditionalFirstCoordinateMean : ℝ :=
  seedConditionalExpectation seedFirstCoordinateMismatch

/-- Conditional first moment of the second mismatch coordinate. -/
def seedConditionalSecondCoordinateMean : ℝ :=
  seedConditionalExpectation seedSecondCoordinateMismatch

/-- Conditional joint second moment of the two mismatch coordinates. -/
def seedConditionalCoordinateJointSecondMoment : ℝ :=
  seedConditionalExpectation (fun p => seedFirstCoordinateMismatch p * seedSecondCoordinateMismatch p)

/-- Conditional covariance of the two coordinate mismatch indicators. -/
def seedConditionalCoordinateCovariance : ℝ :=
  seedConditionalCoordinateJointSecondMoment -
    seedConditionalFirstCoordinateMean * seedConditionalSecondCoordinateMean

/-- Conditional first moment of the total Hamming distance. -/
def seedConditionalHammingMean : ℝ :=
  seedConditionalExpectation (fun p => seedHammingDist p.1 p.2)

/-- Conditional second moment of the total Hamming distance. -/
def seedConditionalHammingSecondMoment : ℝ :=
  seedConditionalExpectation (fun p => (seedHammingDist p.1 p.2 : ℝ) ^ (2 : ℕ))

/-- Conditional variance of the total Hamming distance. -/
def seedConditionalHammingVariance : ℝ :=
  seedConditionalHammingSecondMoment - seedConditionalHammingMean ^ (2 : ℕ)

/-- In the two-bit parity-collision seed, the coordinate mismatch indicators have covariance
`1/4`, and the total Hamming distance has conditional variance `1`.
    prop:fold-collision-conditional-hamming-covariance -/
theorem paper_fold_collision_conditional_hamming_covariance :
    seedConditionalCoordinateCovariance = (1 / 4 : ℝ) ∧
      seedConditionalHammingVariance = (1 : ℝ) := by
  have hFirst : seedConditionalFirstCoordinateMean = (1 / 2 : ℝ) := by
    rw [seedConditionalFirstCoordinateMean, seedConditionalExpectation, twoBitPairs_enum]
    simp [seedCollision, seedHammingDist, seedFirstCoordinateMismatch]
    ring
  have hSecond : seedConditionalSecondCoordinateMean = (1 / 2 : ℝ) := by
    rw [seedConditionalSecondCoordinateMean, seedConditionalExpectation, twoBitPairs_enum]
    simp [seedCollision, seedHammingDist, seedSecondCoordinateMismatch]
    ring
  have hJoint : seedConditionalCoordinateJointSecondMoment = (1 / 2 : ℝ) := by
    rw [seedConditionalCoordinateJointSecondMoment, seedConditionalExpectation, twoBitPairs_enum]
    simp [seedCollision, seedHammingDist, seedFirstCoordinateMismatch, seedSecondCoordinateMismatch]
    ring
  have hHammingMean : seedConditionalHammingMean = (1 : ℝ) := by
    rw [seedConditionalHammingMean, seedConditionalExpectation, twoBitPairs_enum]
    simp [seedCollision, seedHammingDist]
    ring
  have hHammingSecond : seedConditionalHammingSecondMoment = (2 : ℝ) := by
    rw [seedConditionalHammingSecondMoment, seedConditionalExpectation, twoBitPairs_enum]
    simp [seedCollision, seedHammingDist]
    ring
  refine ⟨?_, ?_⟩
  · unfold seedConditionalCoordinateCovariance
    rw [hJoint, hFirst, hSecond]
    norm_num
  · unfold seedConditionalHammingVariance
    rw [hHammingSecond, hHammingMean]
    norm_num

end

end Omega.Folding
