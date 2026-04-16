import Omega.CircleDimension.FiniteFiberAuditExponent

namespace Omega.CircleDimension

/-- A log-auditable phase-circle witness records that the audit exponent is realized exactly at
    `d`. -/
structure LogAuditablePhaseCircleWitness (freeRank torsion d : Nat) : Prop where
  audit_eq : auditExponent freeRank torsion = d

/-- Any value strictly below the circle dimension is obstructed from being a log-auditable
    phase-circle count.
    thm:cdim-minimal-log-auditable-phase-circles -/
def LogAuditablePhaseCircleObstruction (freeRank torsion d : Nat) : Prop :=
  d < circleDim freeRank torsion

/-- Finite audit fibers do not change the witness dimension, so the circle dimension itself is
    always realizable. -/
theorem logAuditablePhaseCircleWitness_cdim (freeRank torsion fiber : Nat) :
    LogAuditablePhaseCircleWitness freeRank (torsion + fiber) (circleDim freeRank torsion) := by
  refine ⟨?_⟩
  calc
    auditExponent freeRank (torsion + fiber) = auditExponent freeRank torsion := by
      exact paper_cdim_finite_fiber_does_not_change_audit_exponent freeRank torsion fiber
    _ = circleDim freeRank torsion := rfl

/-- A strict deficit below the circle dimension rules out an exact audit witness. -/
theorem logAuditablePhaseCircleObstruction_not_witness {freeRank torsion d : Nat}
    (h : LogAuditablePhaseCircleObstruction freeRank torsion d) :
    ¬ LogAuditablePhaseCircleWitness freeRank torsion d := by
  intro hw
  have hEq : circleDim freeRank torsion = d := by
    simpa [auditExponent] using hw.audit_eq
  have : d < d := by
    simpa [LogAuditablePhaseCircleObstruction, hEq] using h
  exact (Nat.lt_irrefl d) this

/-- Paper-facing minimality theorem for log-auditable phase circles: the circle dimension is
    attained, and every smaller candidate is obstructed.
    thm:cdim-minimal-log-auditable-phase-circles -/
theorem paper_cdim_minimal_log_auditable_phase_circles (freeRank torsion fiber : Nat) :
    LogAuditablePhaseCircleWitness freeRank (torsion + fiber) (circleDim freeRank torsion) ∧
      ∀ d : Nat, LogAuditablePhaseCircleObstruction freeRank torsion d →
        ¬ LogAuditablePhaseCircleWitness freeRank torsion d := by
  refine ⟨logAuditablePhaseCircleWitness_cdim freeRank torsion fiber, ?_⟩
  intro d hd
  exact logAuditablePhaseCircleObstruction_not_witness hd

end Omega.CircleDimension
