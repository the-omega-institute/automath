import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.FoldInfoNCELossSpectrumIdentifiability

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- Concrete finite data for the InfoNCE loss-tower reconstruction problem. The loss coefficients
recover the power sums on `2, ..., N`, and the Newton/Prony outputs are modeled as explicit linear
functionals of those recovered power sums. -/
structure FoldInfoNCELossTowerNewtonPronyData where
  N : ℕ
  beta : ℕ → ℕ → ℝ
  spectrumPowerSum : ℕ → ℝ
  lossPowerSum : ℕ → ℝ
  hdiag : ∀ K, 2 ≤ K → K ≤ N → beta K K != 0
  hloss :
    ∀ K, 2 ≤ K → K ≤ N →
      Finset.sum (Finset.Icc 2 K) (fun q => beta K q * spectrumPowerSum q) =
        Finset.sum (Finset.Icc 2 K) (fun q => beta K q * lossPowerSum q)
  newtonSize : ℕ
  newtonKernel : Fin newtonSize → ℕ → ℝ
  pronySize : ℕ
  pronyKernel : Fin pronySize → ℕ → ℝ

namespace FoldInfoNCELossTowerNewtonPronyData

/-- The Newton-reconstructed coefficient indexed by `i`, computed from the recovered power sums. -/
def lossNewtonCoeff (D : FoldInfoNCELossTowerNewtonPronyData) (i : Fin D.newtonSize) : ℝ :=
  Finset.sum (Finset.Icc 2 D.N) fun q => D.newtonKernel i q * D.lossPowerSum q

/-- The corresponding Newton coefficient built from the true spectrum power sums. -/
def spectrumNewtonCoeff (D : FoldInfoNCELossTowerNewtonPronyData) (i : Fin D.newtonSize) : ℝ :=
  Finset.sum (Finset.Icc 2 D.N) fun q => D.newtonKernel i q * D.spectrumPowerSum q

/-- The Prony/Hankel recovered histogram weight indexed by `i`, computed from the recovered power
sums. -/
def lossPronyWeight (D : FoldInfoNCELossTowerNewtonPronyData) (i : Fin D.pronySize) : ℝ :=
  Finset.sum (Finset.Icc 2 D.N) fun q => D.pronyKernel i q * D.lossPowerSum q

/-- The corresponding Prony/Hankel weight built from the true spectrum power sums. -/
def spectrumPronyWeight (D : FoldInfoNCELossTowerNewtonPronyData) (i : Fin D.pronySize) : ℝ :=
  Finset.sum (Finset.Icc 2 D.N) fun q => D.pronyKernel i q * D.spectrumPowerSum q

/-- Completeness of the loss tower: the recovered power sums agree with the spectrum power sums on
the triangular range, and therefore every Newton and Prony linear reconstruction agrees as well. -/
def newtonPronyCompleteness (D : FoldInfoNCELossTowerNewtonPronyData) : Prop :=
  (∀ q, 2 ≤ q → q ≤ D.N → D.lossPowerSum q = D.spectrumPowerSum q) ∧
    (∀ i : Fin D.newtonSize, D.lossNewtonCoeff i = D.spectrumNewtonCoeff i) ∧
    ∀ i : Fin D.pronySize, D.lossPronyWeight i = D.spectrumPronyWeight i

end FoldInfoNCELossTowerNewtonPronyData

open FoldInfoNCELossTowerNewtonPronyData

/-- The existing triangular identifiability theorem recovers the power sums from the InfoNCE loss
tower, and any Newton or Prony reconstruction that is linear in those power sums therefore
reconstructs the same polynomial coefficients and weighted histogram.
    cor:fold-infonce-loss-tower-newton-prony-completeness -/
theorem paper_fold_infonce_loss_tower_newton_prony_completeness
    (D : FoldInfoNCELossTowerNewtonPronyData) : D.newtonPronyCompleteness := by
  have hPower :=
    paper_fold_infonce_loss_spectrum_identifiability D.N D.beta D.spectrumPowerSum D.lossPowerSum
      D.hdiag D.hloss
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hqN
    exact (hPower q hq hqN).symm
  · intro i
    unfold lossNewtonCoeff spectrumNewtonCoeff
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqN : q ≤ D.N := (Finset.mem_Icc.mp hq).2
    rw [(hPower q hq2 hqN).symm]
  · intro i
    unfold lossPronyWeight spectrumPronyWeight
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqN : q ≤ D.N := (Finset.mem_Icc.mp hq).2
    rw [(hPower q hq2 hqN).symm]

end

end Omega.Folding
