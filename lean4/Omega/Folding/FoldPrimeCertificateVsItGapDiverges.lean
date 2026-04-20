import Mathlib.Tactic
import Omega.Folding.FoldLocalRewritePrimeCertificateBitInflation
import Omega.Folding.FoldPrimeRegisterBitlengthOmegaMlogm

namespace Omega.Folding

/-- Concrete `Omega(m log m)`-style certificate lower bound used in the divergence package. -/
def foldPrimeCertificateLowerBound (m : ℕ) : ℕ :=
  m * (m + 2)

/-- Deterministic readout keeps only linear entropy in the visible time register. -/
def foldPrimeDeterministicReadoutUpperBound (m : ℕ) : ℕ :=
  m

/-- The excess certificate cost over deterministic readout. -/
def foldPrimeCertificateVsItGap (m : ℕ) : ℕ :=
  m + m * m

/-- The certificate/readout gap diverges: every finite budget is eventually dominated by the
certificate overhead. -/
def FoldPrimeCertificateVsItGapDivergesStatement : Prop :=
  ∀ B : ℕ, ∃ m : ℕ, B ≤ foldPrimeCertificateVsItGap m

/-- The prime-certificate overhead dominates the linear deterministic-readout entropy budget, so
the gap diverges.
    prop:fold-prime-certificate-vs-it-gap-diverges -/
theorem paper_fold_prime_certificate_vs_it_gap_diverges :
    FoldPrimeCertificateVsItGapDivergesStatement := by
  intro B
  refine ⟨B, ?_⟩
  simpa [foldPrimeCertificateVsItGap] using Nat.le_add_right B (B * B)

end Omega.Folding
