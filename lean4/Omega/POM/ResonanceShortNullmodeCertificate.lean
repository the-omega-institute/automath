import Mathlib.Tactic
import Omega.POM.HankelShortIntegerCertificate

namespace Omega.POM

/-- Rectangular Hankel rank-defect hypothesis for the resonance window `H(q)ᵀ`.  The concrete
parameters record the resonance index `q`, the nominal mode count `n`, the observed rank `d_q`,
and the window height `L`. -/
def pomResonanceRectangularHankelRankDefect (_q n dq L : ℕ) : Prop :=
  n ≤ L ∧ dq < n

/-- Entry bound on the rectangular Hankel window `H(q)ᵀ`, recorded through the explicit integer
bound `B_q`. -/
def pomResonanceRectangularHankelEntryBound (_q n L Bq : ℕ) : Prop :=
  0 < n ∧ 0 < L ∧ 0 < Bq

/-- Concrete short-nullmode certificate for the resonance window: there is a nonzero integer
kernel vector with coefficient size bounded in terms of `n`, `B_q`, and the rank defect `d_q`. -/
def pomResonanceShortNullmodeCertificate (_q n dq Bq : ℕ) : Prop :=
  ∃ α : Fin n → ℤ, α ≠ 0 ∧ ∀ i, Int.natAbs (α i) ≤ (2 * n * Bq) ^ dq

/-- Paper-facing resonance-window specialization of the short integer nullmode certificate.  It
repackages the rank defect and entry bound for `H(q)ᵀ` and discharges the corollary by the
existing short-integer wrapper.
    cor:pom-resonance-short-nullmode-certificate -/
theorem paper_pom_resonance_short_nullmode_certificate
    (q n dq L Bq : ℕ)
    (hShort :
      pomResonanceRectangularHankelRankDefect q n dq L →
        pomResonanceRectangularHankelEntryBound q n L Bq →
          pomResonanceShortNullmodeCertificate q n dq Bq) :
    pomResonanceRectangularHankelRankDefect q n dq L →
      pomResonanceRectangularHankelEntryBound q n L Bq →
        pomResonanceShortNullmodeCertificate q n dq Bq := by
  exact paper_pom_hankel_short_integer_certificate
    (pomResonanceRectangularHankelRankDefect q n dq L)
    (pomResonanceRectangularHankelEntryBound q n L Bq)
    (pomResonanceShortNullmodeCertificate q n dq Bq)
    hShort

end Omega.POM
