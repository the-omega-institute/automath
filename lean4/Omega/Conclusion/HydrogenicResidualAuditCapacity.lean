import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete shell-address parameter for the hydrogenic residual audit count. -/
structure conclusion_hydrogenic_residual_audit_capacity_Data where
  conclusion_hydrogenic_residual_audit_capacity_n : Nat

/-- The coarse `l`-fiber: magnetic labels `m = -l, ..., l` and two spin labels. -/
def conclusion_hydrogenic_residual_audit_capacity_cfFiber
    (D : conclusion_hydrogenic_residual_audit_capacity_Data)
    (l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n) : Type :=
  Fin (2 * l.val + 1) × Bool

instance conclusion_hydrogenic_residual_audit_capacity_cfFiber_fintype
    (D : conclusion_hydrogenic_residual_audit_capacity_Data)
    (l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n) :
    Fintype (conclusion_hydrogenic_residual_audit_capacity_cfFiber D l) := by
  unfold conclusion_hydrogenic_residual_audit_capacity_cfFiber
  infer_instance

/-- The coarse phase-bearing fiber cardinality as a function of `|m| = mu`. -/
def conclusion_hydrogenic_residual_audit_capacity_pbFiberCard
    (_D : conclusion_hydrogenic_residual_audit_capacity_Data) {n : Nat} (_l : Fin n)
    (mu : Fin (_l.val + 1)) : Nat :=
  if (mu : Nat) = 0 then 2 else 4

/-- Direct cardinality of each coarse-field fiber. -/
def conclusion_hydrogenic_residual_audit_capacity_Data.cfFiberCardinality
    (D : conclusion_hydrogenic_residual_audit_capacity_Data) : Prop :=
  ∀ l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n,
    Fintype.card (conclusion_hydrogenic_residual_audit_capacity_cfFiber D l) =
      2 * (2 * l.val + 1)

/-- The maximum coarse-field fiber occurs at the top allowed `l`. -/
def conclusion_hydrogenic_residual_audit_capacity_Data.cfWorstCaseBits
    (D : conclusion_hydrogenic_residual_audit_capacity_Data) : Prop :=
  ∀ l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n,
    Fintype.card (conclusion_hydrogenic_residual_audit_capacity_cfFiber D l) ≤
      4 * D.conclusion_hydrogenic_residual_audit_capacity_n - 2

/-- The phase-bearing fibers have size `2` at `mu = 0` and size `4` otherwise. -/
def conclusion_hydrogenic_residual_audit_capacity_Data.pbFiberCardinality
    (D : conclusion_hydrogenic_residual_audit_capacity_Data) : Prop :=
  ∀ l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n,
    ∀ mu : Fin (l.val + 1),
      conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l mu =
        if (mu : Nat) = 0 then 2 else 4

/-- Residual bits split into spin only at `mu = 0`, and orientation plus spin at `mu > 0`. -/
def conclusion_hydrogenic_residual_audit_capacity_Data.pbResidualBits
    (D : conclusion_hydrogenic_residual_audit_capacity_Data) : Prop :=
  (∀ l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n,
      conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l
        ⟨0, Nat.succ_pos l.val⟩ = 2) ∧
    ∀ l : Fin D.conclusion_hydrogenic_residual_audit_capacity_n,
      ∀ mu : Fin (l.val + 1),
        0 < (mu : Nat) →
          conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l mu = 4

/-- Paper label: `thm:conclusion-hydrogenic-residual-audit-capacity`. -/
theorem paper_conclusion_hydrogenic_residual_audit_capacity
    (D : conclusion_hydrogenic_residual_audit_capacity_Data) :
    D.cfFiberCardinality ∧ D.cfWorstCaseBits ∧ D.pbFiberCardinality ∧ D.pbResidualBits := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    simp [conclusion_hydrogenic_residual_audit_capacity_cfFiber, Nat.mul_comm]
  · intro l
    have hl : l.val < D.conclusion_hydrogenic_residual_audit_capacity_n := l.isLt
    simp [conclusion_hydrogenic_residual_audit_capacity_cfFiber, Nat.mul_comm]
    omega
  · intro l mu
    rfl
  · refine ⟨?_, ?_⟩
    · intro l
      simp [conclusion_hydrogenic_residual_audit_capacity_pbFiberCard]
    · intro l mu hmu
      simp [conclusion_hydrogenic_residual_audit_capacity_pbFiberCard, ne_of_gt hmu]

end Omega.Conclusion
