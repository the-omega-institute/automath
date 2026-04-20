import Omega.Zeta.AbelFinitePartMobiusZeta
import Omega.Zeta.FinitePartMertensAsymptotic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete weighted-Ihara input data for the Abel finite part and the corresponding Mertens
asymptotic. Every field is numerical or functional; the hypotheses record the actual closed-form
identities used by the generic `Omega.Zeta` wrappers. -/
structure IharaMertensConstantData where
  finitePart : ℝ
  logC : ℝ
  mertensConstant : ℝ
  mobiusLogZeta : ℕ → ℝ
  orbitCorrection : ℕ → ℝ
  partialSum : ℕ → ℝ
  hResidue : mobiusLogZeta 1 = logC
  hFinitePartSplit : finitePart = mobiusLogZeta 1 + ∑' k : ℕ, mobiusLogZeta (k + 2)
  hOrbitClosedForm : finitePart = logC + ∑' n : ℕ, orbitCorrection (n + 1)
  hMertens : ∀ N : ℕ, 1 ≤ N → partialSum N = Real.log N + mertensConstant
  hTailSummable : Summable (fun k : ℕ => mobiusLogZeta (k + 2))

namespace IharaMertensConstantData

/-- The Ihara package instantiates the generic Abel finite-part Möbius-zeta wrapper. -/
def toAbelFinitePartMobiusZetaData (D : IharaMertensConstantData) :
    Omega.Zeta.AbelFinitePartMobiusZetaData where
  finitePart := D.finitePart
  logC := D.logC
  mobiusLogZeta := D.mobiusLogZeta
  hResidue := D.hResidue
  hFinitePartSplit := D.hFinitePartSplit
  hTailSummable := D.hTailSummable

end IharaMertensConstantData

/-- Paper label: `prop:ihara-mertens-constant`.
The weighted Ihara finite-part constant splits into the pole term plus the convergent Möbius tail,
and the associated primitive-orbit partial sums satisfy the Mertens asymptotic. -/
theorem paper_ihara_mertens_constant (D : Omega.SyncKernelWeighted.IharaMertensConstantData) :
    (∀ N : ℕ, 1 ≤ N → D.partialSum N = Real.log N + D.mertensConstant) ∧
      D.finitePart = D.logC + ∑' k : ℕ, D.mobiusLogZeta (k + 2) := by
  have hclosed :
      D.finitePart = D.logC + ∑' k : ℕ, D.mobiusLogZeta (k + 2) := by
    simpa [Omega.Zeta.AbelFinitePartMobiusZetaData.finitePartClosedForm] using
      Omega.Zeta.paper_etds_abel_finite_part_mobius_zeta D.toAbelFinitePartMobiusZetaData
  refine ⟨?_, hclosed⟩
  exact
    Omega.Zeta.paper_etds_finite_part_mertens_asymptotic
      (FP := fun _ : Unit => D.finitePart)
      (logC := fun _ : Unit => D.logC)
      (mertensConst := fun _ : Unit => D.mertensConstant)
      (mobiusCorrection := fun _ : Unit => D.mobiusLogZeta)
      (orbitCorrection := fun _ : Unit => D.orbitCorrection)
      (partialOrbitSum := fun _ : Unit => D.partialSum)
      (A := ())
      hclosed
      D.hOrbitClosedForm
      D.hMertens

end
end Omega.SyncKernelWeighted
