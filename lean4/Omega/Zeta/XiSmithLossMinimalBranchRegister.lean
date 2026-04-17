import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Omega.Zeta.SmithEntropyMinDepth

namespace Omega.Zeta

/-- The cardinality of a model affine fiber over a macroscopic `p^k`-projection with
free-kernel contribution `k (n - m)` and Smith contribution `smithEntropy`. -/
def smithFiberCardinality (p n m k : Nat) (smithExponents : Multiset Nat) : Nat :=
  p ^ (k * (n - m) + smithEntropy smithExponents k)

/-- A register size is admissible exactly when it has at least as many labels as a model
affine kernel fiber. This packages the lower-bound side of the minimal branch-register claim. -/
def smithRegisterAdmissible (p n m k : Nat) (smithExponents : Multiset Nat)
    (registerSize : Nat) : Prop :=
  smithFiberCardinality p n m k smithExponents ≤ registerSize

instance instDecidablePredSmithRegisterAdmissible (p n m k : Nat)
    (smithExponents : Multiset Nat) :
    DecidablePred (smithRegisterAdmissible p n m k smithExponents) := by
  intro registerSize
  unfold smithRegisterAdmissible smithFiberCardinality
  infer_instance

/-- The least admissible branch-register size for the Smith profile. -/
def smithMinimalBranchRegister (p n m k : Nat) (smithExponents : Multiset Nat) : Nat :=
  Nat.find
    ⟨smithFiberCardinality p n m k smithExponents,
      show smithRegisterAdmissible p n m k smithExponents
        (smithFiberCardinality p n m k smithExponents) from le_rfl⟩

/-- The least admissible register is exactly the model fiber cardinality, hence
`p^(k (n - m) + smithEntropy)`.
    thm:xi-smith-loss-minimal-branch-register -/
theorem paper_xi_smith_loss_minimal_branch_register
    (p n m k : Nat) (smithExponents : Multiset Nat) :
    smithMinimalBranchRegister p n m k smithExponents =
      p ^ (k * (n - m) + Omega.Zeta.smithEntropy smithExponents k) := by
  change smithMinimalBranchRegister p n m k smithExponents =
    smithFiberCardinality p n m k smithExponents
  refine le_antisymm ?_ ?_
  · unfold smithMinimalBranchRegister
    exact Nat.find_min' ⟨smithFiberCardinality p n m k smithExponents, le_rfl⟩ le_rfl
  · unfold smithMinimalBranchRegister
    exact Nat.find_spec ⟨smithFiberCardinality p n m k smithExponents, le_rfl⟩

end Omega.Zeta
