import Mathlib
import Omega.Folding.FoldPrimeCertificateVsItGapDiverges

namespace Omega.POM

/-- Fixed-`q` macro-moment certificate size: the annihilator/HNF data do not grow with `m`. -/
def macroMomentCertificateSize (q _m : ℕ) : ℕ :=
  q + 1

/-- Micro prime-register certificate size, measured by the concrete fold lower-bound profile. -/
def microPrimeRegisterCertificateSize (m : ℕ) : ℕ :=
  Omega.Folding.foldPrimeCertificateLowerBound m

/-- For fixed `q`, every requested scale ratio is eventually dominated by the micro certificate. -/
def MacroVsMicroPrimeRegisterSeparation (q : ℕ) : Prop :=
  ∀ B : ℕ, ∃ m : ℕ, B * macroMomentCertificateSize q m ≤ microPrimeRegisterCertificateSize m

/-- Paper label:
`thm:pom-macro-moment-vs-micro-prime-register-certificate-separation`. A fixed-`q` macro-moment
certificate stays constant in `m`, while the concrete prime-register certificate lower bound grows
quadratically, hence the scale ratio diverges. -/
theorem paper_pom_macro_moment_vs_micro_prime_register_certificate_separation
    (q : ℕ) (hq : 2 ≤ q) :
    MacroVsMicroPrimeRegisterSeparation q := by
  intro B
  refine ⟨B * (q + 1), ?_⟩
  dsimp [MacroVsMicroPrimeRegisterSeparation, macroMomentCertificateSize,
    microPrimeRegisterCertificateSize, Omega.Folding.foldPrimeCertificateLowerBound]
  have hq1 : 1 ≤ q + 1 := by omega
  nlinarith [Nat.mul_le_mul_left B hq1, hq]

end Omega.POM
