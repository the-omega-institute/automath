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

end

end Omega.Folding
