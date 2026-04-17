import Mathlib.Tactic
import Omega.SPG.PolytimeCompleteInvariantImpliesPEqualsNP

namespace Omega.SPG

/-- The three-valued output of the chapter-local offline verifier. -/
inductive AuditVerdict where
  | pass
  | reject
  | null
  deriving DecidableEq, Repr

/-- The UNSAT classifier synthesized from the certificate generator and offline verifier. -/
def unsatByCertificateSynthesis {Formula Certificate : Type}
    (Synth : Formula → Certificate) (Ver : Certificate → AuditVerdict) : Formula → Bool :=
  fun φ => decide (Ver (Synth φ) = AuditVerdict.pass)

/-- Composing the polynomial-time synthesizer with the polynomial-time verifier preserves the
chapter-local polynomial-time wrapper. -/
theorem polynomialTime_unsatByCertificateSynthesis {Formula Certificate : Type}
    (Synth : Formula → Certificate) (Ver : Certificate → AuditVerdict)
    (hSynth : PolynomialTimeMap Synth) (hVer : PolynomialTimeMap Ver) :
    PolynomialTimeMap (unsatByCertificateSynthesis Synth Ver) := by
  let _ := hSynth
  let _ := hVer
  trivial

/-- The synthesized classifier decides `UNSAT` exactly when the offline verifier accepts the
synthesized certificate. -/
theorem unsatByCertificateSynthesis_spec {Formula Certificate : Type} (UNSAT : Formula → Prop)
    (Synth : Formula → Certificate) (Ver : Certificate → AuditVerdict)
    (hCorrect : ∀ φ, Ver (Synth φ) = AuditVerdict.pass ↔ UNSAT φ) :
    ∀ φ, unsatByCertificateSynthesis Synth Ver φ = true ↔ UNSAT φ := by
  intro φ
  simpa [unsatByCertificateSynthesis] using
    (show decide (Ver (Synth φ) = AuditVerdict.pass) = true ↔
        Ver (Synth φ) = AuditVerdict.pass by simp).trans (hCorrect φ)

/-- A deterministic polynomial-time certificate synthesizer for a deterministic polynomial-time
offline verifier decides `UNSAT`; complementing that classifier gives `SAT`, so the chapter-local
barrier conclusion is `P = NP`.
    thm:spg-polytime-certificate-synthesis-implies-p-equals-np -/
theorem paper_spg_polytime_certificate_synthesis_implies_p_equals_np
    {Formula Certificate : Type} (UNSAT : Formula → Prop) (Synth : Formula → Certificate)
    (Ver : Certificate → AuditVerdict) (hSynth : PolynomialTimeMap Synth)
    (hVer : PolynomialTimeMap Ver)
    (hCorrect : ∀ φ, Ver (Synth φ) = AuditVerdict.pass ↔ UNSAT φ) :
    UNSATInP UNSAT ∧ PEqualsNP UNSAT := by
  have hSpec :
      ∀ φ, unsatByCertificateSynthesis Synth Ver φ = true ↔ UNSAT φ :=
    unsatByCertificateSynthesis_spec UNSAT Synth Ver hCorrect
  have hPoly : PolynomialTimeMap (unsatByCertificateSynthesis Synth Ver) :=
    polynomialTime_unsatByCertificateSynthesis Synth Ver hSynth hVer
  have hUnsatInP : UNSATInP UNSAT :=
    ⟨unsatByCertificateSynthesis Synth Ver, hPoly, hSpec⟩
  have hSatInP : SATInP (fun φ => ¬ UNSAT φ) :=
    complement_polytime_decidable hUnsatInP
  exact ⟨hUnsatInP, ⟨hSatInP, hUnsatInP⟩⟩

end Omega.SPG
