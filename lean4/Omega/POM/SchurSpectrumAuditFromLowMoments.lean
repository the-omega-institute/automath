import Omega.POM.SchurCycleIndexTomography

namespace Omega.POM

open scoped BigOperators

/-- Concrete data for recovering Schur-spectrum audits from low collision moments. -/
structure pom_schur_spectrum_audit_from_low_moments_data where
  Perm : Type
  Part : Type
  permFintype : Fintype Perm
  partFintype : Fintype Part
  q : Nat
  degree : Part → Rat
  character : Part → Perm → Rat
  cycleCollision : Perm → Nat → Rat
  channelTrace : Part → Nat → Rat

namespace pom_schur_spectrum_audit_from_low_moments_data

/-- The trace sequence obtained by the Schur cycle-index formula from low collision moments. -/
def traceFromLowMoments (D : pom_schur_spectrum_audit_from_low_moments_data) :
    D.Part → Nat → Rat := by
  letI := D.permFintype
  exact fun lam m =>
    D.degree lam / (Nat.factorial D.q : Rat) *
      Finset.univ.sum (fun sigma : D.Perm => D.character lam sigma * D.cycleCollision sigma m)

/-- Low moments supply the Schur channel traces through the cycle-index trace formula. -/
def lowMomentTraceFormula (D : pom_schur_spectrum_audit_from_low_moments_data) : Prop := by
  letI := D.permFintype
  exact ∀ lam m,
    D.channelTrace lam m =
      D.degree lam / (Nat.factorial D.q : Rat) *
        Finset.univ.sum (fun sigma : D.Perm =>
          D.character lam sigma * D.cycleCollision sigma m)

/-- Every audit functional depending only on the Schur trace table is recoverable from low moments. -/
def auditRecoverable (D : pom_schur_spectrum_audit_from_low_moments_data) : Prop :=
  ∀ audit : (D.Part → Nat → Rat) → Rat, audit D.channelTrace = audit D.traceFromLowMoments

end pom_schur_spectrum_audit_from_low_moments_data

/-- Paper label: `cor:pom-schur-spectrum-audit-from-low-moments`. -/
theorem paper_pom_schur_spectrum_audit_from_low_moments
    (D : pom_schur_spectrum_audit_from_low_moments_data) :
    D.lowMomentTraceFormula → D.auditRecoverable := by
  intro hLow audit
  letI := D.permFintype
  letI := D.partFintype
  have hTraces :
      ∀ lam m, D.channelTrace lam m = D.traceFromLowMoments lam m := by
    simpa [pom_schur_spectrum_audit_from_low_moments_data.lowMomentTraceFormula,
      pom_schur_spectrum_audit_from_low_moments_data.traceFromLowMoments] using
      paper_pom_schur_cycle_index_tomography (Perm := D.Perm) (Part := D.Part) D.q
        D.degree D.character D.cycleCollision D.channelTrace hLow
  have hTable : D.channelTrace = D.traceFromLowMoments := by
    funext lam m
    exact hTraces lam m
  rw [hTable]

end Omega.POM
