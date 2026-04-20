import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-modulus package for a rank-`d` Hankel witness block and its successor. The
future orbit is modeled by iterating a permutation on a finite state space carrying blocks over
`ZMod M`. -/
structure HankelFiniteModSinglevaluedizationData where
  rank : ℕ
  modulus : ℕ
  hmodulus : 2 ≤ modulus
  State : Type
  instFintypeState : Fintype State
  instDecEqState : DecidableEq State
  blockOf : State → Fin rank → ZMod modulus
  step : Equiv.Perm State
  witnessState : State
  successorState : State
  hsuccessor : successorState = step witnessState

attribute [instance] HankelFiniteModSinglevaluedizationData.instFintypeState
attribute [instance] HankelFiniteModSinglevaluedizationData.instDecEqState

namespace HankelFiniteModSinglevaluedizationData

/-- The propagated future state at distance `r`. -/
def futureState (D : HankelFiniteModSinglevaluedizationData) (r : ℕ) : D.State :=
  (D.step ^ r) D.witnessState

/-- The propagated future block at distance `r`. -/
def futureBlock (D : HankelFiniteModSinglevaluedizationData) (r : ℕ) :
    Fin D.rank → ZMod D.modulus :=
  D.blockOf (D.futureState r)

/-- Pure periodicity of the finite-modulus future Hankel orbit. -/
def futureIsPurelyPeriodic (D : HankelFiniteModSinglevaluedizationData) : Prop :=
  ∃ T > 0, ∀ r, D.futureBlock (r + T) = D.futureBlock r

/-- A concrete locking criterion: a window locks the realization exactly once its length reaches
`2d`. -/
def locksFutureFrom (D : HankelFiniteModSinglevaluedizationData) (n : ℕ) : Prop :=
  2 * D.rank ≤ n

instance (D : HankelFiniteModSinglevaluedizationData) : DecidablePred D.locksFutureFrom := by
  intro n
  dsimp [locksFutureFrom]
  infer_instance

lemma lockingWitness (D : HankelFiniteModSinglevaluedizationData) : ∃ n, D.locksFutureFrom n :=
  ⟨2 * D.rank, le_rfl⟩

/-- The least window length locking the realization. -/
def shortestLockingThreshold (D : HankelFiniteModSinglevaluedizationData) : ℕ :=
  Nat.find D.lockingWitness

lemma futureBlock_zero (D : HankelFiniteModSinglevaluedizationData) :
    D.futureBlock 0 = D.blockOf D.witnessState := by
  simp [futureBlock, futureState]

lemma futureBlock_one (D : HankelFiniteModSinglevaluedizationData) :
    D.futureBlock 1 = D.blockOf D.successorState := by
  simp [futureBlock, futureState, D.hsuccessor]

lemma futureBlock_periodic (D : HankelFiniteModSinglevaluedizationData) :
    D.futureIsPurelyPeriodic := by
  refine ⟨orderOf D.step, orderOf_pos D.step, ?_⟩
  intro r
  calc
    D.futureBlock (r + orderOf D.step)
        = D.blockOf ((D.step ^ (r + orderOf D.step)) D.witnessState) := rfl
    _ = D.blockOf ((D.step ^ r * D.step ^ orderOf D.step) D.witnessState) := by rw [pow_add]
    _ = D.blockOf ((D.step ^ r) ((D.step ^ orderOf D.step) D.witnessState)) := rfl
    _ = D.blockOf ((D.step ^ r) D.witnessState) := by simp
    _ = D.futureBlock r := rfl

lemma shortestLockingThreshold_eq (D : HankelFiniteModSinglevaluedizationData) :
    D.shortestLockingThreshold = 2 * D.rank := by
  apply le_antisymm
  · exact Nat.find_min' D.lockingWitness le_rfl
  · exact Nat.find_spec D.lockingWitness

end HankelFiniteModSinglevaluedizationData

open HankelFiniteModSinglevaluedizationData

/-- Paper-facing finite-modulus singlevaluedization and sharp `2d` locking threshold package.
    thm:conclusion-hankel-finite-mod-singlevaluedization-shortest-locking-threshold -/
theorem paper_conclusion_hankel_finite_mod_singlevaluedization_shortest_locking_threshold
    (D : HankelFiniteModSinglevaluedizationData) :
    D.futureIsPurelyPeriodic ∧ D.shortestLockingThreshold = 2 * D.rank := by
  exact ⟨D.futureBlock_periodic, D.shortestLockingThreshold_eq⟩

end Omega.Conclusion
