import Mathlib.Tactic

namespace Omega.StableArithmetic.MedialityFailure

abbrev stable_audit_mediality_failure_carrier := Fin 36

/-- The audited finite operation, restricted to the table entries used by the witness. -/
def stable_audit_mediality_failure_op
    (x y : stable_audit_mediality_failure_carrier) :
    stable_audit_mediality_failure_carrier :=
  match x.val, y.val with
  | 0, 0 => ⟨17, by decide⟩
  | 9, 0 => ⟨0, by decide⟩
  | 17, 0 => ⟨28, by decide⟩
  | 0, 9 => ⟨0, by decide⟩
  | 0, 17 => ⟨32, by decide⟩
  | _, _ => ⟨0, by decide⟩

def stable_audit_mediality_failure_medial
    (op : stable_audit_mediality_failure_carrier →
      stable_audit_mediality_failure_carrier →
      stable_audit_mediality_failure_carrier) : Prop :=
  ∀ a b c d : stable_audit_mediality_failure_carrier,
    op (op a b) (op c d) = op (op a c) (op b d)

/-- prop:stable-audit-mediality-failure -/
theorem paper_stable_audit_mediality_failure :
    ¬ stable_audit_mediality_failure_medial stable_audit_mediality_failure_op := by
  intro h
  have hWitness :=
    h (0 : stable_audit_mediality_failure_carrier)
      (0 : stable_audit_mediality_failure_carrier)
      (9 : stable_audit_mediality_failure_carrier)
      (0 : stable_audit_mediality_failure_carrier)
  norm_num [stable_audit_mediality_failure_medial, stable_audit_mediality_failure_op] at hWitness

end Omega.StableArithmetic.MedialityFailure
