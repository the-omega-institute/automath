import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Omega.GU.TerminalFoldbin6PushforwardMarkov
import Omega.GU.TerminalFoldbin6ThreeOffsetRigidity
import Omega.GU.Window6P6CompactnessPrinciple
import Omega.TypedAddressBiaxialCompletion.CertificateLoop

namespace Omega.GU

open Matrix
open Omega.TypedAddressBiaxialCompletion

/-- The audited window-`6`, `p = 6` pushforward kernel already carries the concrete row-sum and
detailed-balance identities from the terminal Markov certificate. -/
def window6P6PushforwardMarkovLaw : Prop :=
  let π : Fin 21 → ℚ := fun i => (cBinFiberMult 6 (X.ofNat 6 i) : ℚ) / 64
  let P : Fin 21 → Fin 21 → ℚ := fun i j =>
    (cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ) /
      (6 * cBinFiberMult 6 (X.ofNat 6 i))
  (∀ i, (Finset.univ : Finset (Fin 21)).sum (P i) = 1) ∧
    ∀ i j, π i * P i j = π j * P j i

/-- Concrete finite-field selfadjoint witness used to instantiate the abstract compactness wrapper
with actual matrix data. -/
structure Window6P6ToeplitzCertificateChainData where
  commutantWitness : Matrix (Fin 21) (Fin 21) (ZMod 2)
  commutantWitness_selfadjoint : commutantWitness.transpose = commutantWitness
  certificateLoop : TypedAddressCertificateLoopData
  spectralLeft : ℝ
  spectralRight : ℝ
  spectralPhase : ℝ
  spectralPhase_mem : spectralPhase ∈ Set.Icc spectralLeft spectralRight
  completedCharpoly : Polynomial ℂ
  completedCharpoly_phaseRoot :
    completedCharpoly.eval (Complex.exp (spectralPhase * Complex.I)) = 0

/-- The chosen finite-field witness is symmetric, hence selfadjoint. -/
def window6P6Selfadjoint (D : Window6P6ToeplitzCertificateChainData) : Prop :=
  D.commutantWitness.transpose = D.commutantWitness

/-- Finite-dimensionality of the ambient audited `21 × 21` matrix packet. -/
def window6P6FiniteDimensional : Prop :=
  FiniteDimensional (ZMod 2) (Fin 21 → ZMod 2)

/-- The finite commutant packet used as the concrete compactness target. -/
def window6P6FiniteCommutant (D : Window6P6ToeplitzCertificateChainData) : Prop :=
  Finite {A : Matrix (Fin 21) (Fin 21) (ZMod 2) // A * D.commutantWitness = D.commutantWitness * A}

/-- The recorded phase lies in the certified spectral interval. -/
def window6P6PhaseInSpectralInterval (D : Window6P6ToeplitzCertificateChainData) : Prop :=
  D.spectralPhase ∈ Set.Icc D.spectralLeft D.spectralRight

/-- The completed characteristic polynomial has a unit-circle root produced from the certified
phase. -/
def window6P6UnitCircleRoot (D : Window6P6ToeplitzCertificateChainData) : Prop :=
  ∃ z : ℂ, D.completedCharpoly.eval z = 0 ∧ ‖z‖ = 1

/-- Combined certificate chain for the window-`6`, `p = 6` Toeplitz package: the pushforward
kernel is Markov and reversible, the finite commutant packet is compact in the chapter's concrete
finite-field model, the Toeplitz certificate loop closes, the Zeckendorf tail offsets are rigid,
and the completed characteristic polynomial has a unit-circle root coming from the spectral
interval.
    thm:window6-p6-toeplitz-certificate-chain -/
def Window6P6ToeplitzCertificateChain (D : Window6P6ToeplitzCertificateChainData) : Prop :=
  window6P6PushforwardMarkovLaw ∧
    window6P6Selfadjoint D ∧
    window6P6FiniteCommutant D ∧
    (D.certificateLoop.rh ↔ D.certificateLoop.jensenDefectZeroLimit) ∧
    (D.certificateLoop.jensenDefectZeroLimit ↔ D.certificateLoop.repulsionRadiusTendsToOne) ∧
    (D.certificateLoop.repulsionRadiusTendsToOne ↔ D.certificateLoop.toeplitzPsdAll) ∧
    (D.certificateLoop.toeplitzPsdAll ↔ D.certificateLoop.toeplitzPsdCofinal) ∧
    terminalFoldbin6TailOffset ⟨true, false, false⟩ = Nat.fib 8 ∧
    terminalFoldbin6TailOffset ⟨false, true, false⟩ = Nat.fib 9 ∧
    terminalFoldbin6TailOffset ⟨false, false, true⟩ = Nat.fib 10 ∧
    cBinFiberHist 6 1 = 0 ∧
    cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = 21 ∧
    window6P6PhaseInSpectralInterval D ∧
    window6P6UnitCircleRoot D

theorem paper_window6_p6_toeplitz_certificate_chain
    (D : Window6P6ToeplitzCertificateChainData) : Window6P6ToeplitzCertificateChain D := by
  have hCompactness :
      window6P6Selfadjoint D ∧ window6P6FiniteCommutant D := by
    refine paper_window6_p6_compactness_principle
      (selfadjoint := window6P6Selfadjoint D)
      (finiteDim := window6P6FiniteDimensional)
      (commutantStarAlg := window6P6FiniteCommutant D)
      (unitaryCompact := window6P6FiniteCommutant D)
      D.commutantWitness_selfadjoint
      (by
        dsimp [window6P6FiniteDimensional]
        infer_instance)
      (by
        intro _ _
        dsimp [window6P6FiniteCommutant]
        infer_instance)
      (by intro h; exact h)
  have hLoop := paper_typed_address_biaxial_completion_certificate_loop D.certificateLoop
  have hZeckendorf := paper_terminal_foldbin6_three_offset_rigidity
  have hUnitRoot : window6P6UnitCircleRoot D := by
    refine ⟨Complex.exp (D.spectralPhase * Complex.I), D.completedCharpoly_phaseRoot, ?_⟩
    simp
  rcases hZeckendorf with ⟨h8, h9, h10, hHist1, hHist234⟩
  refine ⟨paper_terminal_foldbin6_pushforward_markov, hCompactness.1, hCompactness.2,
    hLoop.1, hLoop.2.1, hLoop.2.2.1, hLoop.2.2.2, h8, h9, h10, hHist1, hHist234,
    D.spectralPhase_mem, hUnitRoot⟩

end Omega.GU
