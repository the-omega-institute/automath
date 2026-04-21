import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Rat.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

private lemma prime_dvd_nextDet_natAbs_of_prime_dvd_futureDet_natAbs
    (d k0 n : ℕ) (H : ℕ → Matrix (Fin d) (Fin d) ℤ) (A : Matrix (Fin d) (Fin d) ℚ)
    (hprop : ∀ r, (H (k0 + r)).det = (H k0).det * A.det ^ r)
    (hA : A.det = (H (k0 + 1)).det / (H k0).det)
    {p : ℕ} (hp : Nat.Prime p) (hdet0 : (H k0).det ≠ 0)
    (hdiv : p ∣ (H (k0 + n.succ)).det.natAbs) :
    p ∣ (H (k0 + 1)).det.natAbs := by
  let det0 : ℤ := (H k0).det
  let det1 : ℤ := (H (k0 + 1)).det
  let detn : ℤ := (H (k0 + n.succ)).det
  have hdet0q : ((det0 : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hdet0
  have hratio : A.det = (det1 : ℚ) / (det0 : ℚ) := by
    simpa [det0, det1] using hA
  have hratio_pow :
      ∀ m : ℕ, (det0 : ℚ) * ((det1 : ℚ) / (det0 : ℚ)) ^ m.succ =
        ((det1 : ℚ) ^ m.succ) / ((det0 : ℚ) ^ m) := by
    intro m
    rw [div_pow, pow_succ, div_eq_mul_inv]
    field_simp [hdet0q]
    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  have hfuture :
      (detn : ℚ) = ((det1 : ℚ) ^ n.succ) / ((det0 : ℚ) ^ n) := by
    calc
      (detn : ℚ) = (det0 : ℚ) * A.det ^ n.succ := by
        simpa [det0, detn] using hprop n.succ
      _ = (det0 : ℚ) * (((det1 : ℚ) / (det0 : ℚ)) ^ n.succ) := by rw [hratio]
      _ = ((det1 : ℚ) ^ n.succ) / ((det0 : ℚ) ^ n) := hratio_pow n
  have hdivInt : (p : ℤ) ∣ detn := by
    exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hdiv)
  have hnumdvd : (Rat.num (Rat.divInt (det1 ^ n.succ) (det0 ^ n)) : ℤ) ∣ det1 ^ n.succ := by
    exact Rat.num_dvd _ (pow_ne_zero _ hdet0)
  have hnum_eq : Rat.num (Rat.divInt (det1 ^ n.succ) (det0 ^ n)) = detn := by
    rw [← Rat.intCast_div_eq_divInt]
    calc
      Rat.num ((((det1 ^ n.succ : ℤ) : ℚ) / ((det0 ^ n : ℤ) : ℚ))) = Rat.num (detn : ℚ) := by
        simpa [Int.cast_pow] using congrArg Rat.num hfuture.symm
      _ = detn := Rat.num_intCast detn
  have hdetn_dvd : detn ∣ det1 ^ n.succ := by
    simpa [hnum_eq] using hnumdvd
  have hpdvdpowInt : (p : ℤ) ∣ det1 ^ n.succ := dvd_trans hdivInt hdetn_dvd
  have hpdvdpowNat : p ∣ (det1.natAbs) ^ n.succ := by
    have hpdvdpowAbs : p ∣ (det1 ^ n.succ).natAbs := by
      exact Int.natCast_dvd_natCast.1 (Int.dvd_natAbs.2 hpdvdpowInt)
    simpa [Int.natAbs_pow] using hpdvdpowAbs
  exact hp.dvd_of_dvd_pow hpdvdpowNat

/-- Paper label: `cor:conclusion-hankel-mod-degeneration-finite-bad-prime-localization`.
Every prime dividing any propagated Hankel determinant already divides the product of the initial
determinant and its immediate successor. -/
theorem paper_conclusion_hankel_mod_degeneration_finite_bad_prime_localization
    (d k0 : ℕ) (H : ℕ → Matrix (Fin d) (Fin d) ℤ) (A : Matrix (Fin d) (Fin d) ℚ)
    (hprop : ∀ r, (H (k0 + r)).det = (H k0).det * A.det ^ r)
    (hA : A.det = (H (k0 + 1)).det / (H k0).det) :
    ∀ (r p : ℕ), Nat.Prime p → p ∣ (H (k0 + r)).det.natAbs →
      p ∣ (((H k0).det * (H (k0 + 1)).det).natAbs) := by
  intro r p hp hdiv
  cases r with
  | zero =>
      simpa [Int.natAbs_mul] using
        dvd_mul_of_dvd_left hdiv (H (k0 + 1)).det.natAbs
  | succ n =>
      by_cases hdet0 : (H k0).det = 0
      · simp [hdet0]
      · have hnext :
            p ∣ (H (k0 + 1)).det.natAbs :=
          prime_dvd_nextDet_natAbs_of_prime_dvd_futureDet_natAbs d k0 n H A hprop hA hp hdet0 hdiv
        simpa [Int.natAbs_mul, mul_comm, mul_left_comm, mul_assoc] using
          dvd_mul_of_dvd_right hnext (H k0).det.natAbs

end Omega.Conclusion
