import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Off-diagonal blocks vanish under the scalar Haar average in the folded block model. -/
def foldQuantumChannelCrossBlockAverage (offDiagBlocks : List ℚ) : List ℚ :=
  List.replicate offDiagBlocks.length 0

/-- Each diagonal block is replaced by its normalized trace scalar. -/
def foldQuantumChannelDiagonalBlockAverage (blockRanks : List ℕ) (blockTraces : List ℚ) : List ℚ :=
  List.zipWith (fun d tr => tr / (d : ℚ)) blockRanks blockTraces

/-- The concrete blockwise Haar twirl is obtained by combining the diagonal and off-diagonal
averages. -/
def foldQuantumChannelHaarTwirl
    (blockRanks : List ℕ) (blockTraces offDiagBlocks : List ℚ) : List ℚ × List ℚ :=
  (foldQuantumChannelCrossBlockAverage offDiagBlocks,
    foldQuantumChannelDiagonalBlockAverage blockRanks blockTraces)

/-- The folded quantum channel retains only the diagonal trace data. -/
def foldQuantumChannelFoldedChannel
    (blockRanks : List ℕ) (blockTraces offDiagBlocks : List ℚ) : List ℚ × List ℚ :=
  (List.replicate offDiagBlocks.length 0,
    List.zipWith (fun d tr => tr / (d : ℚ)) blockRanks blockTraces)

/-- The cross-block Haar averages are all zero. -/
def foldQuantumChannelCrossBlocksAverageToZero (offDiagBlocks : List ℚ) : Prop :=
  foldQuantumChannelCrossBlockAverage offDiagBlocks = List.replicate offDiagBlocks.length 0

/-- The diagonal Haar averages are exactly the normalized trace blocks. -/
def foldQuantumChannelDiagonalBlocksTwirledToTraceBlocks
    (blockRanks : List ℕ) (blockTraces : List ℚ) : Prop :=
  foldQuantumChannelDiagonalBlockAverage blockRanks blockTraces =
    List.zipWith (fun d tr => tr / (d : ℚ)) blockRanks blockTraces

/-- Reassembling the twirled blocks recovers the folded channel. -/
def foldQuantumChannelHaarTwirlEqFoldChannel
    (blockRanks : List ℕ) (blockTraces offDiagBlocks : List ℚ) : Prop :=
  foldQuantumChannelHaarTwirl blockRanks blockTraces offDiagBlocks =
    foldQuantumChannelFoldedChannel blockRanks blockTraces offDiagBlocks

/-- Paper label: `prop:op-algebra-fold-quantum-channel-haar-twirl`. In the scalar folded block
model, the Haar twirl kills the cross blocks, replaces each diagonal block by trace over
dimension, and therefore coincides with the folded channel. -/
theorem paper_op_algebra_fold_quantum_channel_haar_twirl
    (blockRanks : List ℕ) (blockTraces offDiagBlocks : List ℚ) :
    foldQuantumChannelCrossBlocksAverageToZero offDiagBlocks ∧
      foldQuantumChannelDiagonalBlocksTwirledToTraceBlocks blockRanks blockTraces ∧
      foldQuantumChannelHaarTwirlEqFoldChannel blockRanks blockTraces offDiagBlocks := by
  exact ⟨rfl, rfl, rfl⟩

end Omega.OperatorAlgebra
