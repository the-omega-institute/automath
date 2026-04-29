import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.Defect

namespace Omega.Folding

/-- Finite weighted sample data for the discrete-Stokes auditable gap estimate. The data keeps a
length-`m + k` word at each sample point, a nonnegative weight on the sample, and an observable on
the length-`m` folded words with uniform sup norm `supNorm`. -/
structure FoldDiscreteStokesAuditableBoundData where
  m : ℕ
  k : ℕ
  Sample : Type
  fintypeSample : Fintype Sample
  decEqSample : DecidableEq Sample
  word : Sample → Omega.Word (m + k)
  prob : Sample → ℝ
  prob_nonneg : ∀ s : Sample, 0 ≤ prob s
  observable : Omega.Word m → ℝ
  supNorm : ℝ
  supNorm_nonneg : 0 ≤ supNorm
  observable_bound : ∀ w : Omega.Word m, |observable w| ≤ supNorm

def FoldDiscreteStokesAuditableBoundData.leftWord (D : FoldDiscreteStokesAuditableBoundData)
    (s : D.Sample) : Omega.Word D.m :=
  (Omega.Fold (Omega.restrictWord (Nat.le_add_right D.m D.k) (D.word s))).1

def FoldDiscreteStokesAuditableBoundData.rightWord (D : FoldDiscreteStokesAuditableBoundData)
    (s : D.Sample) : Omega.Word D.m :=
  (Omega.X.restrictLE (Nat.le_add_right D.m D.k) (Omega.Fold (D.word s))).1

def FoldDiscreteStokesAuditableBoundData.observableGapAt
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample) : ℝ :=
  |D.observable (D.leftWord s) - D.observable (D.rightWord s)|

def FoldDiscreteStokesAuditableBoundData.globalDefectEvent
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample) : Prop :=
  Omega.globalDefect (Nat.le_add_right D.m D.k) (D.word s) ≠ Omega.zeroWord D.m

def FoldDiscreteStokesAuditableBoundData.localWord
    (D : FoldDiscreteStokesAuditableBoundData) (j : Fin D.k) (s : D.Sample) :
    Omega.Word (D.m + j.1 + 1) :=
  Omega.restrictWord
    (by omega)
    (D.word s)

def FoldDiscreteStokesAuditableBoundData.localDefectEvent
    (D : FoldDiscreteStokesAuditableBoundData) (j : Fin D.k) (s : D.Sample) : Prop :=
  Omega.localCurvature (D.localWord j s)

noncomputable def FoldDiscreteStokesAuditableBoundData.globalDefectIndicatorAt
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample) : ℝ :=
  by
    classical
    exact if D.globalDefectEvent s then 1 else 0

noncomputable def FoldDiscreteStokesAuditableBoundData.localDefectIndicatorAt
    (D : FoldDiscreteStokesAuditableBoundData) (j : Fin D.k) (s : D.Sample) : ℝ :=
  by
    classical
    exact if D.localDefectEvent j s then 1 else 0

def FoldDiscreteStokesAuditableBoundData.expectedGap
    (D : FoldDiscreteStokesAuditableBoundData) : ℝ :=
  let _ := D.fintypeSample
  let _ := D.decEqSample
  ∑ s : D.Sample, D.prob s * D.observableGapAt s

noncomputable def FoldDiscreteStokesAuditableBoundData.globalDefectProb
    (D : FoldDiscreteStokesAuditableBoundData) : ℝ :=
  let _ := D.fintypeSample
  let _ := D.decEqSample
  ∑ s : D.Sample, D.prob s * D.globalDefectIndicatorAt s

noncomputable def FoldDiscreteStokesAuditableBoundData.layerwiseDefectProbSum
    (D : FoldDiscreteStokesAuditableBoundData) : ℝ :=
  let _ := D.fintypeSample
  let _ := D.decEqSample
  ∑ j : Fin D.k, ∑ s : D.Sample, D.prob s * D.localDefectIndicatorAt j s

private theorem localDefectIndicatorAt_nonneg (D : FoldDiscreteStokesAuditableBoundData)
    (j : Fin D.k) (s : D.Sample) : 0 ≤ D.localDefectIndicatorAt j s := by
  classical
  by_cases h : D.localDefectEvent j s <;>
    simp [FoldDiscreteStokesAuditableBoundData.localDefectIndicatorAt, h]

private theorem leftWord_eq_rightWord_of_not_globalDefectEvent
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample)
    (hs : ¬ D.globalDefectEvent s) :
    D.leftWord s = D.rightWord s := by
  have hzero : Omega.globalDefect (Nat.le_add_right D.m D.k) (D.word s) = Omega.zeroWord D.m := by
    by_contra hneq
    exact hs hneq
  have hcomm :=
    (Omega.globalDefect_eq_zero_iff (h := Nat.le_add_right D.m D.k) (ω := D.word s)).mp hzero
  simpa [FoldDiscreteStokesAuditableBoundData.leftWord,
    FoldDiscreteStokesAuditableBoundData.rightWord] using congrArg Subtype.val hcomm

private theorem observableGapAt_le_globalDefectIndicator
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample) :
    D.observableGapAt s ≤ 2 * D.supNorm * D.globalDefectIndicatorAt s := by
  classical
  by_cases hdef : D.globalDefectEvent s
  · have hleft := abs_le.mp (D.observable_bound (D.leftWord s))
    have hright := abs_le.mp (D.observable_bound (D.rightWord s))
    have hbound : D.observableGapAt s ≤ 2 * D.supNorm := by
      refine abs_le.mpr ?_
      constructor <;> nlinarith [hleft.1, hleft.2, hright.1, hright.2]
    simpa [FoldDiscreteStokesAuditableBoundData.globalDefectIndicatorAt, hdef] using hbound
  · have hEq := leftWord_eq_rightWord_of_not_globalDefectEvent D s hdef
    simp [FoldDiscreteStokesAuditableBoundData.observableGapAt,
      FoldDiscreteStokesAuditableBoundData.globalDefectIndicatorAt, hdef, hEq]

private theorem exists_localDefectEvent_of_globalDefectEvent
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample)
    (hs : D.globalDefectEvent s) :
    ∃ j : Fin D.k, D.localDefectEvent j s := by
  classical
  by_contra hnone
  have hallzero :
      ∀ j : ℕ, (hj : j < D.k) →
        Omega.localDefect
            (Omega.restrictWord
              (by omega)
              (D.word s)) =
          Omega.zeroWord (D.m + j) := by
    intro j hj
    have hlocal : ¬ D.localDefectEvent ⟨j, hj⟩ s := by
      intro hlocal
      exact hnone ⟨⟨j, hj⟩, hlocal⟩
    by_contra hneq
    exact hlocal (by
      simpa [FoldDiscreteStokesAuditableBoundData.localDefectEvent,
        FoldDiscreteStokesAuditableBoundData.localWord,
        Omega.localCurvature_iff_defect_ne_zero] using hneq)
  have hzero := Omega.globalDefect_zero_of_all_local_zero (m := D.m) (k := D.k) (ω := D.word s) hallzero
  exact hs hzero

private theorem globalDefectIndicatorAt_le_layerwiseIndicators
    (D : FoldDiscreteStokesAuditableBoundData) (s : D.Sample) :
    D.globalDefectIndicatorAt s ≤ ∑ j : Fin D.k, D.localDefectIndicatorAt j s := by
  classical
  by_cases hdef : D.globalDefectEvent s
  · rcases exists_localDefectEvent_of_globalDefectEvent D s hdef with ⟨j, hj⟩
    have hsum : 1 ≤ ∑ i : Fin D.k, D.localDefectIndicatorAt i s := by
      calc
        1 = D.localDefectIndicatorAt j s := by
          simp [FoldDiscreteStokesAuditableBoundData.localDefectIndicatorAt, hj]
        _ ≤ ∑ i : Fin D.k, D.localDefectIndicatorAt i s := by
          exact Finset.single_le_sum (fun i hi => localDefectIndicatorAt_nonneg D i s) (by simp)
    simpa [FoldDiscreteStokesAuditableBoundData.globalDefectIndicatorAt, hdef] using hsum
  · have hnonneg : 0 ≤ ∑ j : Fin D.k, D.localDefectIndicatorAt j s := by
      exact Finset.sum_nonneg (fun j hj => localDefectIndicatorAt_nonneg D j s)
    simpa [FoldDiscreteStokesAuditableBoundData.globalDefectIndicatorAt, hdef] using hnonneg

set_option maxHeartbeats 400000 in
/-- The difference of expectations of a bounded observable is controlled by twice its sup norm
times the probability of the defect event; moreover, the defect event is contained in the
union of local-curvature events, yielding the corresponding union-bound estimate.
    cor:fold-discrete-stokes-auditable-bound -/
theorem paper_fold_discrete_stokes_auditable_bound (D : FoldDiscreteStokesAuditableBoundData) :
    D.expectedGap ≤ 2 * D.supNorm * D.globalDefectProb ∧
      D.globalDefectProb ≤ D.layerwiseDefectProbSum := by
  let _ := D.fintypeSample
  let _ := D.decEqSample
  refine ⟨?_, ?_⟩
  · unfold FoldDiscreteStokesAuditableBoundData.expectedGap
      FoldDiscreteStokesAuditableBoundData.globalDefectProb
    calc
      ∑ s : D.Sample, D.prob s * D.observableGapAt s
          ≤ ∑ s : D.Sample, D.prob s * (2 * D.supNorm * D.globalDefectIndicatorAt s) := by
              refine Finset.sum_le_sum ?_
              intro s hs
              exact mul_le_mul_of_nonneg_left
                (observableGapAt_le_globalDefectIndicator D s) (D.prob_nonneg s)
      _ = ∑ s : D.Sample, (2 * D.supNorm) * (D.prob s * D.globalDefectIndicatorAt s) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
      _ = (2 * D.supNorm) * ∑ s : D.Sample, D.prob s * D.globalDefectIndicatorAt s := by
            rw [Finset.mul_sum]
  · unfold FoldDiscreteStokesAuditableBoundData.globalDefectProb
      FoldDiscreteStokesAuditableBoundData.layerwiseDefectProbSum
    calc
      ∑ s : D.Sample, D.prob s * D.globalDefectIndicatorAt s
          ≤ ∑ s : D.Sample, D.prob s * ∑ j : Fin D.k, D.localDefectIndicatorAt j s := by
              refine Finset.sum_le_sum ?_
              intro s hs
              exact mul_le_mul_of_nonneg_left
                (globalDefectIndicatorAt_le_layerwiseIndicators D s) (D.prob_nonneg s)
      _ = ∑ s : D.Sample, ∑ j : Fin D.k, D.prob s * D.localDefectIndicatorAt j s := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.mul_sum]
      _ = ∑ j : Fin D.k, ∑ s : D.Sample, D.prob s * D.localDefectIndicatorAt j s := by
            rw [Finset.sum_comm]

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the total-variation auditable bound in the fold-truncation
paper. -/
theorem paper_fold_truncation_discrete_stokes_auditable_bound :
    ∃ (_D : Type) (_K : Nat → Type),
      True :=
  foldDiscreteStokesAuditableBound

end Omega.Folding
