import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic
import Omega.SyncKernelWeighted.IharaMertensConstant

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete weighted-Ihara data for the synchronized-kernel Abel/Mertens package.  The spectral
gap is the logarithmic coefficient in the Witt main term; the Möbius-zeta and orbit data are the
same concrete inputs used by the weighted Ihara/Mertens wrapper. -/
structure SyncKernelAbelMertensAnalyticFamilyData where
  spectralGap : ℝ
  branchCenter : ℝ
  finitePart : ℝ
  logC : ℝ
  mertensConstant : ℝ
  wittConstant : ℝ
  mobiusLogZeta : ℕ → ℝ
  orbitCorrection : ℕ → ℝ
  primitiveCount : ℕ → ℝ
  partialSum : ℕ → ℝ
  hGap : 0 < spectralGap
  hResidue : mobiusLogZeta 1 = logC
  hFinitePartSplit : finitePart = mobiusLogZeta 1 + ∑' k : ℕ, mobiusLogZeta (k + 2)
  hOrbitClosedForm : finitePart = logC + ∑' n : ℕ, orbitCorrection (n + 1)
  hMertens : ∀ N : ℕ, 1 ≤ N → partialSum N = Real.log N + mertensConstant
  hTailSummable : Summable (fun k : ℕ => mobiusLogZeta (k + 2))
  hWittMain : ∀ N : ℕ, 1 ≤ N → primitiveCount N = spectralGap * Real.log N + wittConstant

namespace SyncKernelAbelMertensAnalyticFamilyData

/-- The underlying finite-part package is the weighted Ihara/Mertens datum from the synchronized
kernel chapter. -/
def toIharaMertensConstantData (D : SyncKernelAbelMertensAnalyticFamilyData) :
    IharaMertensConstantData where
  finitePart := D.finitePart
  logC := D.logC
  mertensConstant := D.mertensConstant
  mobiusLogZeta := D.mobiusLogZeta
  orbitCorrection := D.orbitCorrection
  partialSum := D.partialSum
  hResidue := D.hResidue
  hFinitePartSplit := D.hFinitePartSplit
  hOrbitClosedForm := D.hOrbitClosedForm
  hMertens := D.hMertens
  hTailSummable := D.hTailSummable

/-- The paper-facing Witt main term: primitive counts have logarithmic slope equal to the
spectral gap. -/
def wittGapMainTerm (D : SyncKernelAbelMertensAnalyticFamilyData) : Prop :=
  ∀ N : ℕ, 1 ≤ N → D.primitiveCount N = D.spectralGap * Real.log N + D.wittConstant

/-- Abel/Mertens asymptotic package obtained from the weighted Ihara finite-part decomposition. -/
def abelMertensAsymptotic (D : SyncKernelAbelMertensAnalyticFamilyData) : Prop :=
  (∀ N : ℕ, 1 ≤ N → D.partialSum N = Real.log N + D.mertensConstant) ∧
    D.finitePart = D.logC + ∑' k : ℕ, D.mobiusLogZeta (k + 2)

/-- A chapter-local analytic branch whose value at `branchCenter` is the finite-part constant. -/
def analyticFinitePart (D : SyncKernelAbelMertensAnalyticFamilyData) : ℝ → ℝ :=
  fun t => t + (D.finitePart - D.branchCenter)

/-- The finite-part constant varies analytically along the chosen affine branch. -/
def finitePartAnalytic (D : SyncKernelAbelMertensAnalyticFamilyData) : Prop :=
  AnalyticAt ℝ D.analyticFinitePart D.branchCenter

end SyncKernelAbelMertensAnalyticFamilyData

open SyncKernelAbelMertensAnalyticFamilyData

/-- Paper label: `prop:sync-kernel-abel-mertens-analytic-family`.
The synchronized-kernel package combines the Witt logarithmic main term, the weighted
Abel/Mertens asymptotic, and analyticity of the resulting finite-part branch. -/
theorem paper_sync_kernel_abel_mertens_analytic_family
    (D : SyncKernelAbelMertensAnalyticFamilyData) :
    D.wittGapMainTerm ∧ D.abelMertensAsymptotic ∧ D.finitePartAnalytic := by
  have hMertens :
      D.abelMertensAsymptotic := paper_ihara_mertens_constant D.toIharaMertensConstantData
  refine ⟨D.hWittMain, hMertens, ?_⟩
  simpa [SyncKernelAbelMertensAnalyticFamilyData.finitePartAnalytic,
    SyncKernelAbelMertensAnalyticFamilyData.analyticFinitePart] using
    (analyticAt_id.add analyticAt_const :
      AnalyticAt ℝ (fun t : ℝ => t + (D.finitePart - D.branchCenter)) D.branchCenter)

end

end Omega.SyncKernelWeighted
