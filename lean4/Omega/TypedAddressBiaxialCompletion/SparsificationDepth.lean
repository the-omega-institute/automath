import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CertificateLoop
import Omega.TypedAddressBiaxialCompletion.ComovingBitBudget
import Omega.TypedAddressBiaxialCompletion.CompiledReadability
import Omega.TypedAddressBiaxialCompletion.JensenCountableCriterion
import Omega.TypedAddressBiaxialCompletion.NonNullRequiresThreeAxes

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete data for the sparsification-depth package. The record ties together the countable
Jensen sparsification criterion, the compiled Toeplitz--PSD truncation certificate, and the depth
resources needed to turn a non-`NULL` typed certificate into a hard resource bound. -/
structure SparsificationDepthData where
  jensenCriterion : JensenCountableCriterionData
  certificateLoop : TypedAddressCertificateLoopData
  criterionCofinalWitness : ∀ n : ℕ, jensenCriterion.defect (jensenCriterion.rhoSeq n) = 0
  criterionRhToLoopRh : jensenCriterion.rh → certificateLoop.rh
  compiledCertificate : CompiledToeplitzPsdCertificate
  radius : ℝ
  hradius_nonneg : 0 ≤ radius
  hradius_lt_one : radius < 1
  T : ℝ
  δ : ℝ
  p : ℝ
  γ : ℝ
  hT : 1 ≤ T
  hδ : 0 < δ
  hγ : |γ| ≤ T
  hres : (2 : ℝ) ^ (-p) ≤ typedAddressWorstCaseDepth T δ
  compiledReadabilityData : CompiledReadabilityData
  readable_h : compiledReadabilityData.readable
  threeAxisData : TypedAddressThreeAxisData
  nonNullReadout_h : threeAxisData.nonNullReadout

namespace SparsificationDepthData

/-- Cofinal vanishing along the Jensen sparsification sequence forces the cofinal Toeplitz--PSD
certificate exported by the chapter's loop theorem. -/
def toeplitzPsdCofinalSparsification (D : SparsificationDepthData) : Prop :=
  D.certificateLoop.toeplitzPsdCofinal

/-- The finite truncation order already eliminates the infinite quantifier package by exporting a
scalar PSD witness, a nonnegative Carathéodory lower buffer, a positive Schur delta, and a strict
Schur contraction at the chosen compiled radius. -/
def finiteQuantifierElimination (D : SparsificationDepthData) : Prop :=
  compiledToeplitzTrueBlockPsd D.compiledCertificate ∧
    0 ≤ compiledToeplitzCaratheodoryLowerBound D.compiledCertificate D.radius ∧
    0 < compiledToeplitzSchurDelta D.compiledCertificate D.radius ∧
    compiledToeplitzSchurBound D.compiledCertificate D.radius < 1

/-- The depth statement is a hard resource bound: the dyadic budget dominates the worst-case
depth threshold, the compiled witness provides a nonempty certificate fiber, and a non-`NULL`
readout forces all three orthogonal axis passes. -/
def depthHardResource (D : SparsificationDepthData) : Prop :=
  typedAddressWorstCaseBitBudget D.T D.δ ≤ D.p ∧
    D.compiledReadabilityData.certificateFiberNonempty ∧
    D.threeAxisData.visibleAxisPassed ∧
    D.threeAxisData.residueAxisPassed ∧
    D.threeAxisData.modeAxisPassed

end SparsificationDepthData

/-- Paper-facing sparsification-depth wrapper: the countable Jensen sparsification theorem feeds
the certificate loop and yields the cofinal Toeplitz--PSD clause, the finite compiled certificate
discharges the truncation/oracle-collapse package, and the bit-budget plus non-`NULL` lemmas give
the hard depth resource statement.
    prop:typed-address-biaxial-completion-sparsification-depth -/
theorem paper_typed_address_biaxial_completion_sparsification_depth
    (D : SparsificationDepthData) :
    D.toeplitzPsdCofinalSparsification ∧ D.finiteQuantifierElimination ∧ D.depthHardResource := by
  have hSparseRh : D.jensenCriterion.rh :=
    (paper_app_jensen_countable_criterion D.jensenCriterion).2 D.criterionCofinalWitness
  have hLoopRh : D.certificateLoop.rh := D.criterionRhToLoopRh hSparseRh
  have hLoop := paper_typed_address_biaxial_completion_certificate_loop D.certificateLoop
  have hLoopJensen : D.certificateLoop.jensenDefectZeroLimit := (hLoop.1).mp hLoopRh
  have hLoopRep : D.certificateLoop.repulsionRadiusTendsToOne := (hLoop.2.1).mp hLoopJensen
  have hLoopToeplitzAll : D.certificateLoop.toeplitzPsdAll := (hLoop.2.2.1).mp hLoopRep
  have hLoopToeplitzCofinal : D.certificateLoop.toeplitzPsdCofinal := (hLoop.2.2.2).mp hLoopToeplitzAll
  have hFinite :
      compiledToeplitzTrueBlockPsd D.compiledCertificate ∧
        0 ≤ compiledToeplitzCaratheodoryLowerBound D.compiledCertificate D.radius ∧
        0 < compiledToeplitzSchurDelta D.compiledCertificate D.radius ∧
        compiledToeplitzSchurBound D.compiledCertificate D.radius < 1 :=
    paper_typed_address_biaxial_completion_compiled_psd_certificate
      D.compiledCertificate D.hradius_nonneg D.hradius_lt_one
  have hDepthBudget :
      typedAddressFixedChartDepth D.δ D.γ ≥ typedAddressWorstCaseDepth D.T D.δ ∧
        typedAddressWorstCaseBitBudget D.T D.δ ≤ D.p ∧
        2 * Real.logb 2 D.T - Real.logb 2 (4 * D.δ) ≤ typedAddressWorstCaseBitBudget D.T D.δ ∧
        typedAddressWorstCaseBitBudget D.T D.δ ≤
          2 * Real.logb 2 (D.T + (1 + D.δ)) - Real.logb 2 (4 * D.δ) :=
    paper_typed_address_biaxial_completion_comoving_bit_budget D.hT D.hδ D.hγ D.hres
  have hReadable :
      D.compiledReadabilityData.readable ↔
        D.compiledReadabilityData.addressAdmitted ∧
          D.compiledReadabilityData.cechObstructionVanishes ∧
            D.compiledReadabilityData.thresholdsMet ∧
            D.compiledReadabilityData.certificateFiberNonempty :=
    paper_typed_address_biaxial_completion_compiled_readability_readable D.compiledReadabilityData
  have hFiber : D.compiledReadabilityData.certificateFiberNonempty :=
    (hReadable.mp D.readable_h).2.2.2
  have hAxes :
      D.threeAxisData.visibleAxisPassed ∧
        D.threeAxisData.residueAxisPassed ∧
        D.threeAxisData.modeAxisPassed :=
    paper_typed_address_biaxial_completion_nonnull_requires_three_axes
      D.threeAxisData D.nonNullReadout_h
  refine ⟨hLoopToeplitzCofinal, hFinite, ?_⟩
  exact ⟨hDepthBudget.2.1, hFiber, hAxes.1, hAxes.2.1, hAxes.2.2⟩

end Omega.TypedAddressBiaxialCompletion
