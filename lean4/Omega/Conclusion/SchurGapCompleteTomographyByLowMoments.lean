import Mathlib.Tactic
import Omega.POM.SchurCycleIndexTomography

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite Schur/Frobenius data: `Perm` is the finite cycle-type side, `Part` is the
finite Schur partition side, and the recovery map is an explicit inverse readout from Schur traces
back to low moments. -/
structure conclusion_schur_gap_complete_tomography_by_low_moments_data where
  conclusion_schur_gap_complete_tomography_by_low_moments_perm : Type
  conclusion_schur_gap_complete_tomography_by_low_moments_part : Type
  conclusion_schur_gap_complete_tomography_by_low_moments_perm_fintype :
    Fintype conclusion_schur_gap_complete_tomography_by_low_moments_perm
  conclusion_schur_gap_complete_tomography_by_low_moments_part_fintype :
    Fintype conclusion_schur_gap_complete_tomography_by_low_moments_part
  conclusion_schur_gap_complete_tomography_by_low_moments_q : ℕ
  conclusion_schur_gap_complete_tomography_by_low_moments_degree :
    conclusion_schur_gap_complete_tomography_by_low_moments_part → ℚ
  conclusion_schur_gap_complete_tomography_by_low_moments_character :
    conclusion_schur_gap_complete_tomography_by_low_moments_part →
      conclusion_schur_gap_complete_tomography_by_low_moments_perm → ℚ
  conclusion_schur_gap_complete_tomography_by_low_moments_cycleCollision :
    conclusion_schur_gap_complete_tomography_by_low_moments_perm → ℕ → ℚ
  conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace :
    conclusion_schur_gap_complete_tomography_by_low_moments_part → ℕ → ℚ
  conclusion_schur_gap_complete_tomography_by_low_moments_recoverMoment :
    (conclusion_schur_gap_complete_tomography_by_low_moments_part → ℕ → ℚ) →
      conclusion_schur_gap_complete_tomography_by_low_moments_perm → ℕ → ℚ
  conclusion_schur_gap_complete_tomography_by_low_moments_trace_formula_h :
    ∀ lam m,
      conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace lam m =
        conclusion_schur_gap_complete_tomography_by_low_moments_degree lam /
            (Nat.factorial conclusion_schur_gap_complete_tomography_by_low_moments_q : ℚ) *
          (@Finset.univ conclusion_schur_gap_complete_tomography_by_low_moments_perm
              conclusion_schur_gap_complete_tomography_by_low_moments_perm_fintype).sum
            (fun sigma =>
              conclusion_schur_gap_complete_tomography_by_low_moments_character lam sigma *
                conclusion_schur_gap_complete_tomography_by_low_moments_cycleCollision sigma m)
  conclusion_schur_gap_complete_tomography_by_low_moments_recover_h :
    ∀ sigma m,
      conclusion_schur_gap_complete_tomography_by_low_moments_recoverMoment
          conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace sigma m =
        conclusion_schur_gap_complete_tomography_by_low_moments_cycleCollision sigma m

/-- The Schur trace table computed from the finite Frobenius character expansion. -/
def conclusion_schur_gap_complete_tomography_by_low_moments_data.traceFromLowMoments
    (D : conclusion_schur_gap_complete_tomography_by_low_moments_data) :
    D.conclusion_schur_gap_complete_tomography_by_low_moments_part → ℕ → ℚ :=
  fun lam m =>
    D.conclusion_schur_gap_complete_tomography_by_low_moments_degree lam /
        (Nat.factorial D.conclusion_schur_gap_complete_tomography_by_low_moments_q : ℚ) *
      (@Finset.univ D.conclusion_schur_gap_complete_tomography_by_low_moments_perm
          D.conclusion_schur_gap_complete_tomography_by_low_moments_perm_fintype).sum
        (fun sigma =>
          D.conclusion_schur_gap_complete_tomography_by_low_moments_character lam sigma *
            D.conclusion_schur_gap_complete_tomography_by_low_moments_cycleCollision sigma m)

/-- The finite Frobenius character trace formula for every Schur partition and moment index. -/
def conclusion_schur_gap_complete_tomography_by_low_moments_data.lowMomentTraceFormula
    (D : conclusion_schur_gap_complete_tomography_by_low_moments_data) : Prop :=
  ∀ lam m,
    D.conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace lam m =
      D.traceFromLowMoments lam m

/-- The inverse reconstruction clause: the explicit readout recovers the low moments. -/
def conclusion_schur_gap_complete_tomography_by_low_moments_data.inverseReconstruction
    (D : conclusion_schur_gap_complete_tomography_by_low_moments_data) : Prop :=
  ∀ sigma m,
    D.conclusion_schur_gap_complete_tomography_by_low_moments_recoverMoment
        D.conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace sigma m =
      D.conclusion_schur_gap_complete_tomography_by_low_moments_cycleCollision sigma m

/-- Any scalar audit of the Schur trace table is determined by the low moments. -/
def conclusion_schur_gap_complete_tomography_by_low_moments_data.auditRecoverable
    (D : conclusion_schur_gap_complete_tomography_by_low_moments_data) : Prop :=
  ∀ audit :
      (D.conclusion_schur_gap_complete_tomography_by_low_moments_part → ℕ → ℚ) → ℚ,
    audit D.conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace =
      audit D.traceFromLowMoments

/-- Paper-facing Schur-gap tomography package. -/
def conclusion_schur_gap_complete_tomography_by_low_moments_data.Holds
    (D : conclusion_schur_gap_complete_tomography_by_low_moments_data) : Prop :=
  D.lowMomentTraceFormula ∧ D.inverseReconstruction ∧ D.auditRecoverable

/-- Paper label: `thm:conclusion-schur-gap-complete-tomography-by-low-moments`. -/
theorem paper_conclusion_schur_gap_complete_tomography_by_low_moments
    (D : conclusion_schur_gap_complete_tomography_by_low_moments_data) : D.Holds := by
  letI := D.conclusion_schur_gap_complete_tomography_by_low_moments_perm_fintype
  letI := D.conclusion_schur_gap_complete_tomography_by_low_moments_part_fintype
  have hTraceFormula :
      D.lowMomentTraceFormula := by
    simpa [
      conclusion_schur_gap_complete_tomography_by_low_moments_data.lowMomentTraceFormula,
      conclusion_schur_gap_complete_tomography_by_low_moments_data.traceFromLowMoments] using
      Omega.POM.paper_pom_schur_cycle_index_tomography
        (Perm := D.conclusion_schur_gap_complete_tomography_by_low_moments_perm)
        (Part := D.conclusion_schur_gap_complete_tomography_by_low_moments_part)
        D.conclusion_schur_gap_complete_tomography_by_low_moments_q
        D.conclusion_schur_gap_complete_tomography_by_low_moments_degree
        D.conclusion_schur_gap_complete_tomography_by_low_moments_character
        D.conclusion_schur_gap_complete_tomography_by_low_moments_cycleCollision
        D.conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace
        D.conclusion_schur_gap_complete_tomography_by_low_moments_trace_formula_h
  have hInverse :
      D.inverseReconstruction := by
    simpa [
      conclusion_schur_gap_complete_tomography_by_low_moments_data.inverseReconstruction] using
      D.conclusion_schur_gap_complete_tomography_by_low_moments_recover_h
  have hAudit :
      D.auditRecoverable := by
    intro audit
    have hTable :
        D.conclusion_schur_gap_complete_tomography_by_low_moments_channelTrace =
          D.traceFromLowMoments := by
      funext lam m
      exact hTraceFormula lam m
    rw [hTable]
  exact ⟨hTraceFormula, hInverse, hAudit⟩

end Omega.Conclusion
