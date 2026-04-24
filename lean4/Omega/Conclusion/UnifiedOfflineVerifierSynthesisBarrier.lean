import Omega.SPG.PolytimeCertificateSynthesisImpliesPEqualsNP

namespace Omega.Conclusion

open Omega.SPG

universe u v

/-- Concrete data for the conclusion-level synthesis barrier: formulas, synthesized certificates,
the three-valued offline verifier, and the `UNSAT` predicate tracked by the paper statement. -/
structure UnifiedOfflineVerifierSynthesisBarrierData where
  Formula : Type u
  Certificate : Type v
  UNSAT : Formula → Prop
  Synth : Formula → Certificate
  Ver : Certificate → AuditVerdict

namespace UnifiedOfflineVerifierSynthesisBarrierData

/-- The synthesizer and offline verifier both run in the chapter-local polynomial-time wrapper. -/
def polytimeSynth (D : UnifiedOfflineVerifierSynthesisBarrierData) : Prop :=
  PolynomialTimeMap D.Synth ∧ PolynomialTimeMap D.Ver

/-- The synthesized certificate is accepted exactly for unsatisfiable formulas. -/
def verifierAcceptsIffUnsat (D : UnifiedOfflineVerifierSynthesisBarrierData) : Prop :=
  ∀ φ, D.Ver (D.Synth φ) = AuditVerdict.pass ↔ D.UNSAT φ

/-- The conclusion of the synthesis barrier. -/
def P_eq_NP (D : UnifiedOfflineVerifierSynthesisBarrierData) : Prop :=
  PEqualsNP D.UNSAT

end UnifiedOfflineVerifierSynthesisBarrierData

open UnifiedOfflineVerifierSynthesisBarrierData

/-- Paper label: `thm:conclusion-unified-offline-verifier-synthesis-barrier`. -/
theorem paper_conclusion_unified_offline_verifier_synthesis_barrier
    (D : UnifiedOfflineVerifierSynthesisBarrierData) :
    D.polytimeSynth →
      D.verifierAcceptsIffUnsat →
        D.P_eq_NP := by
  intro hPoly hCorrect
  rcases hPoly with ⟨hSynth, hVer⟩
  exact
    (paper_spg_polytime_certificate_synthesis_implies_p_equals_np
      D.UNSAT D.Synth D.Ver hSynth hVer hCorrect).2

end Omega.Conclusion
