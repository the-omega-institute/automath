import Mathlib.Tactic

namespace Omega.Folding

/-- The stable reservoir block `1000`. -/
def blockReservoirStableBlock : List Bool :=
  [true, false, false, false]

/-- The active block `0110`, which rewrites to `1000` inside a single block. -/
def blockReservoirActiveBlock : List Bool :=
  [false, true, true, false]

/-- Block encoder for a single source bit. -/
def blockReservoirEncodeBlock (b : Bool) : List Bool :=
  if b then blockReservoirActiveBlock else blockReservoirStableBlock

/-- Concatenate the block encoding of an input bitstring. -/
def blockReservoirEncode : List Bool → List Bool
  | [] => []
  | b :: bs => blockReservoirEncodeBlock b ++ blockReservoirEncode bs

/-- The constant-radius reservoir word `(1000)^k`. -/
def blockReservoirWord : ℕ → List Bool
  | 0 => []
  | k + 1 => blockReservoirStableBlock ++ blockReservoirWord k

/-- Blockwise normalization that rewrites `0110` to `1000` and leaves every other
4-bit block unchanged. -/
def blockReservoirFold : List Bool → List Bool
  | a :: b :: c :: d :: rest =>
      (if [a, b, c, d] = blockReservoirActiveBlock then blockReservoirStableBlock
        else [a, b, c, d]) ++ blockReservoirFold rest
  | tail => tail

/-- Decoder for a single 4-bit block: it reads `1` exactly on `0110`. -/
def blockReservoirDecodeBlock (a b c d : Bool) : Bool :=
  decide ([a, b, c, d] = blockReservoirActiveBlock)

/-- Decoder obtained by reading the encoded word blockwise. -/
def blockReservoirDecode : List Bool → List Bool
  | a :: b :: c :: d :: rest =>
      blockReservoirDecodeBlock a b c d :: blockReservoirDecode rest
  | _ => []

/-- Cross-block windows of length three are never `011`; the only possible boundary windows are
the two windows straddling consecutive 4-bit blocks. -/
def blockReservoirNoCrossBlock011Between (b c : Bool) : Prop :=
  let left := blockReservoirEncodeBlock b
  let right := blockReservoirEncodeBlock c
  left.drop 2 ++ right.take 1 ≠ [false, true, true] ∧
    left.drop 3 ++ right.take 2 ≠ [false, true, true]

/-- Recursive package asserting that no consecutive encoded blocks create a cross-block `011`. -/
def blockReservoirNoCrossBlock011 : List Bool → Prop
  | [] => True
  | [_] => True
  | b :: c :: rest =>
      blockReservoirNoCrossBlock011Between b c ∧ blockReservoirNoCrossBlock011 (c :: rest)

/-- Pointwise xor on equal-length lists, truncating if the lengths differ. -/
def blockReservoirListXor : List Bool → List Bool → List Bool
  | [], [] => []
  | a :: as, b :: bs => decide (a ≠ b) :: blockReservoirListXor as bs
  | _, _ => []

/-- Hamming weight of a Boolean list. -/
def blockReservoirHammingWeight (bits : List Bool) : ℕ :=
  bits.count true

/-- Concrete paper package for the block reservoir encoding. -/
def blockReservoirEncodingConstantRadius : Prop :=
  (∀ w, blockReservoirFold (blockReservoirEncode w) = blockReservoirWord w.length) ∧
    (∀ w, blockReservoirNoCrossBlock011 w) ∧
    (∀ w, blockReservoirDecode (blockReservoirEncode w) = w) ∧
    Function.Injective blockReservoirEncode ∧
    (∀ w w', w.length = w'.length →
      blockReservoirHammingWeight
          (blockReservoirListXor (blockReservoirEncode w) (blockReservoirEncode w')) =
        3 * blockReservoirHammingWeight (blockReservoirListXor w w'))

@[simp] theorem blockReservoirFold_active :
    blockReservoirFold blockReservoirActiveBlock = blockReservoirStableBlock := by
  decide

@[simp] theorem blockReservoirFold_stable :
    blockReservoirFold blockReservoirStableBlock = blockReservoirStableBlock := by
  decide

@[simp] theorem blockReservoirDecode_encodeBlock (b : Bool) :
    blockReservoirDecode (blockReservoirEncodeBlock b) = [b] := by
  cases b <;> decide

theorem blockReservoirNoCrossBlock011Between_all (b c : Bool) :
    blockReservoirNoCrossBlock011Between b c := by
  cases b <;> cases c <;>
    unfold blockReservoirNoCrossBlock011Between blockReservoirEncodeBlock
      blockReservoirActiveBlock blockReservoirStableBlock <;> decide

theorem blockReservoirFold_encode :
    ∀ w : List Bool,
      blockReservoirFold (blockReservoirEncode w) = blockReservoirWord w.length
  | [] => rfl
  | b :: bs => by
      cases b <;>
        simp [blockReservoirEncode, blockReservoirFold, blockReservoirWord,
          blockReservoirEncodeBlock, blockReservoirActiveBlock, blockReservoirStableBlock,
          blockReservoirFold_encode bs]

theorem blockReservoirNoCrossBlock011_encode :
    ∀ w : List Bool, blockReservoirNoCrossBlock011 w
  | [] => trivial
  | [_] => trivial
  | b :: c :: rest =>
      ⟨blockReservoirNoCrossBlock011Between_all b c, blockReservoirNoCrossBlock011_encode (c :: rest)⟩

@[simp] theorem blockReservoirDecode_encode :
    ∀ w : List Bool, blockReservoirDecode (blockReservoirEncode w) = w
  | [] => rfl
  | b :: bs => by
      cases b <;>
        simp [blockReservoirEncode, blockReservoirDecode, blockReservoirEncodeBlock,
          blockReservoirDecode_encode bs, blockReservoirActiveBlock, blockReservoirStableBlock,
          blockReservoirDecodeBlock]

theorem blockReservoirEncode_injective :
    Function.Injective blockReservoirEncode := by
  intro w w' h
  have hDecode := congrArg blockReservoirDecode h
  simpa using hDecode

@[simp] theorem blockReservoirHammingWeight_xor_encodeBlock (a b : Bool) :
    blockReservoirHammingWeight
        (blockReservoirListXor (blockReservoirEncodeBlock a) (blockReservoirEncodeBlock b)) =
      if a = b then 0 else 3 := by
  cases a <;> cases b <;> native_decide

theorem blockReservoirHammingWeight_xor_encode :
    ∀ {w w' : List Bool}, w.length = w'.length →
      blockReservoirHammingWeight
          (blockReservoirListXor (blockReservoirEncode w) (blockReservoirEncode w')) =
        3 * blockReservoirHammingWeight (blockReservoirListXor w w')
  | [], [], _ => by
      simp [blockReservoirEncode, blockReservoirListXor, blockReservoirHammingWeight]
  | [], _ :: _, hlen => by
      cases hlen
  | _ :: _, [], hlen => by
      cases hlen
  | a :: as, b :: bs, hlen => by
      have htail : as.length = bs.length := by simpa using Nat.succ.inj hlen
      have ih := blockReservoirHammingWeight_xor_encode htail
      cases a <;> cases b
      · simpa [blockReservoirEncode, blockReservoirEncodeBlock, blockReservoirListXor,
          blockReservoirHammingWeight, blockReservoirActiveBlock, blockReservoirStableBlock] using ih
      · simp [blockReservoirEncode, blockReservoirEncodeBlock, blockReservoirListXor,
          blockReservoirHammingWeight, blockReservoirActiveBlock, blockReservoirStableBlock] at ih ⊢
        omega
      · simp [blockReservoirEncode, blockReservoirEncodeBlock, blockReservoirListXor,
          blockReservoirHammingWeight, blockReservoirActiveBlock, blockReservoirStableBlock] at ih ⊢
        omega
      · simpa [blockReservoirEncode, blockReservoirEncodeBlock, blockReservoirListXor,
          blockReservoirHammingWeight, blockReservoirActiveBlock, blockReservoirStableBlock] using ih

/-- The block reservoir encoding folds blockwise to the constant reservoir word, has no cross-block
`011`, decodes exactly, is injective, and multiplies Hamming distance by `3`.
    thm:fold-block-reservoir-encoding-constant-radius -/
theorem paper_fold_block_reservoir_encoding_constant_radius :
    blockReservoirEncodingConstantRadius := by
  refine ⟨blockReservoirFold_encode, blockReservoirNoCrossBlock011_encode,
    blockReservoirDecode_encode, blockReservoirEncode_injective, ?_⟩
  intro w w' hlen
  exact blockReservoirHammingWeight_xor_encode hlen

end Omega.Folding
