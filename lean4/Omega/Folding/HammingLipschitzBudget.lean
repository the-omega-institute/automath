import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.HammingDist

namespace Omega.Folding

/-- The recursive layerwise Hamming budget obtained by summing the popcounts of the projected
local defects appearing in the discrete-Stokes xor decomposition. -/
def foldLayerwiseBudget (m : Nat) : ∀ k : Nat, Omega.Word (m + k) → Nat
  | 0, _ => 0
  | k + 1, ω =>
      Omega.popcount (Omega.restrictWord (Nat.le_add_right m k) (Omega.localDefect ω)) +
        foldLayerwiseBudget m k (Omega.truncate ω)

theorem popcount_defectChain_le_foldLayerwiseBudget (m : Nat) :
    ∀ k : Nat, ∀ ω : Omega.Word (m + k),
      Omega.popcount (Omega.defectChain m k ω) ≤ foldLayerwiseBudget m k ω
  | 0, ω => by
      simp [foldLayerwiseBudget, Omega.defectChain, Omega.popcount, Omega.wordSupport,
        Omega.zeroWord]
  | k + 1, ω => by
      simp [foldLayerwiseBudget, Omega.defectChain]
      calc
        Omega.popcount
            (Omega.xorWord
              (Omega.restrictWord (Nat.le_add_right m k) (Omega.localDefect ω))
              (Omega.defectChain m k (Omega.truncate ω)))
            ≤ Omega.popcount (Omega.restrictWord (Nat.le_add_right m k) (Omega.localDefect ω)) +
              Omega.popcount (Omega.defectChain m k (Omega.truncate ω)) :=
          Omega.popcount_xorWord_le _ _
        _ ≤ Omega.popcount (Omega.restrictWord (Nat.le_add_right m k) (Omega.localDefect ω)) +
              foldLayerwiseBudget m k (Omega.truncate ω) := by
            exact Nat.add_le_add_left
              (popcount_defectChain_le_foldLayerwiseBudget m k (Omega.truncate ω)) _

theorem popcount_globalDefect_le_foldLayerwiseBudget (m k : Nat) (ω : Omega.Word (m + k)) :
    Omega.popcount (Omega.globalDefect (Nat.le_add_right m k) ω) ≤ foldLayerwiseBudget m k ω := by
  rw [Omega.globalDefect_eq_defectChain]
  exact popcount_defectChain_le_foldLayerwiseBudget m k ω

/-- Concrete finite-sample data for the Hamming--Lipschitz defect budget. The sample carries
weights, a length-`m + k` word at each sample point, and an observable on length-`m` words with a
uniform Hamming-Lipschitz constant `L`. -/
structure FoldHammingLipschitzBudgetData where
  m : ℕ
  k : ℕ
  Sample : Type
  fintypeSample : Fintype Sample
  decEqSample : DecidableEq Sample
  word : Sample → Omega.Word (m + k)
  prob : Sample → ℝ
  prob_nonneg : ∀ s : Sample, 0 ≤ prob s
  observable : Omega.Word m → ℝ
  L : ℝ
  lipschitz :
    ∀ a b : Omega.Word m, |observable a - observable b| ≤ L * (Omega.hammingDist a b : ℝ)

def FoldHammingLipschitzBudgetData.leftWord (D : FoldHammingLipschitzBudgetData) (s : D.Sample) :
    Omega.Word D.m :=
  (Omega.Fold (Omega.restrictWord (Nat.le_add_right D.m D.k) (D.word s))).1

def FoldHammingLipschitzBudgetData.rightWord (D : FoldHammingLipschitzBudgetData) (s : D.Sample) :
    Omega.Word D.m :=
  (Omega.X.restrictLE (Nat.le_add_right D.m D.k) (Omega.Fold (D.word s))).1

def FoldHammingLipschitzBudgetData.observableGapAt
    (D : FoldHammingLipschitzBudgetData) (s : D.Sample) : ℝ :=
  |D.observable (D.leftWord s) - D.observable (D.rightWord s)|

def FoldHammingLipschitzBudgetData.defectWeightAt
    (D : FoldHammingLipschitzBudgetData) (s : D.Sample) : ℝ :=
  (Omega.popcount (Omega.globalDefect (Nat.le_add_right D.m D.k) (D.word s)) : ℝ)

def FoldHammingLipschitzBudgetData.layerwiseBudgetAt
    (D : FoldHammingLipschitzBudgetData) (s : D.Sample) : ℝ :=
  (foldLayerwiseBudget D.m D.k (D.word s) : ℝ)

def FoldHammingLipschitzBudgetData.expectedObservableGap
    (D : FoldHammingLipschitzBudgetData) : ℝ :=
  let _ := D.fintypeSample
  let _ := D.decEqSample
  ∑ s : D.Sample, D.prob s * D.observableGapAt s

def FoldHammingLipschitzBudgetData.expectedDefectWeight
    (D : FoldHammingLipschitzBudgetData) : ℝ :=
  let _ := D.fintypeSample
  let _ := D.decEqSample
  ∑ s : D.Sample, D.prob s * D.defectWeightAt s

def FoldHammingLipschitzBudgetData.expectedLayerwiseBudget
    (D : FoldHammingLipschitzBudgetData) : ℝ :=
  let _ := D.fintypeSample
  let _ := D.decEqSample
  ∑ s : D.Sample, D.prob s * D.layerwiseBudgetAt s

/-- Expected observable gap is bounded by the Lipschitz constant times the expected global
defect size. -/
def FoldHammingLipschitzBudgetData.observableGapBound
    (D : FoldHammingLipschitzBudgetData) : Prop :=
  D.expectedObservableGap ≤ D.L * D.expectedDefectWeight

/-- Expected global defect size is bounded by the expected layerwise Stokes budget. -/
def FoldHammingLipschitzBudgetData.layerwiseDefectBudgetBound
    (D : FoldHammingLipschitzBudgetData) : Prop :=
  D.expectedDefectWeight ≤ D.expectedLayerwiseBudget

private theorem observableGapAt_le_defectWeightAt
    (D : FoldHammingLipschitzBudgetData) (s : D.Sample) :
    D.observableGapAt s ≤ D.L * D.defectWeightAt s := by
  have hLip := D.lipschitz (D.leftWord s) (D.rightWord s)
  have hDist :
      Omega.hammingDist (D.leftWord s) (D.rightWord s) =
        Omega.popcount (Omega.globalDefect (Nat.le_add_right D.m D.k) (D.word s)) := by
    simpa [FoldHammingLipschitzBudgetData.leftWord, FoldHammingLipschitzBudgetData.rightWord,
      Omega.globalDefect] using
      (Omega.hammingDist_eq_popcount_xor (D.leftWord s) (D.rightWord s))
  simpa [FoldHammingLipschitzBudgetData.observableGapAt,
    FoldHammingLipschitzBudgetData.defectWeightAt, hDist] using hLip

private theorem defectWeightAt_le_layerwiseBudgetAt
    (D : FoldHammingLipschitzBudgetData) (s : D.Sample) :
    D.defectWeightAt s ≤ D.layerwiseBudgetAt s := by
  have hNat :
      Omega.popcount (Omega.globalDefect (Nat.le_add_right D.m D.k) (D.word s)) ≤
        foldLayerwiseBudget D.m D.k (D.word s) :=
    popcount_globalDefect_le_foldLayerwiseBudget D.m D.k (D.word s)
  simpa [FoldHammingLipschitzBudgetData.defectWeightAt,
    FoldHammingLipschitzBudgetData.layerwiseBudgetAt] using (show
      (Omega.popcount (Omega.globalDefect (Nat.le_add_right D.m D.k) (D.word s)) : ℝ) ≤
        (foldLayerwiseBudget D.m D.k (D.word s) : ℝ) from by
          exact_mod_cast hNat)

/-- Hamming--Lipschitz budget package: the expected observable gap is controlled by the expected
global defect size, and the latter is bounded by the expected layerwise discrete-Stokes budget.
    cor:fold-hamming-lipschitz-budget -/
theorem paper_fold_hamming_lipschitz_budget (D : FoldHammingLipschitzBudgetData) :
    D.observableGapBound ∧ D.layerwiseDefectBudgetBound := by
  let _ := D.fintypeSample
  let _ := D.decEqSample
  refine ⟨?_, ?_⟩
  · unfold FoldHammingLipschitzBudgetData.observableGapBound
      FoldHammingLipschitzBudgetData.expectedObservableGap
      FoldHammingLipschitzBudgetData.expectedDefectWeight
    calc
      ∑ s : D.Sample, D.prob s * D.observableGapAt s
          ≤ ∑ s : D.Sample, D.prob s * (D.L * D.defectWeightAt s) := by
              refine Finset.sum_le_sum ?_
              intro s hs
              exact mul_le_mul_of_nonneg_left
                (observableGapAt_le_defectWeightAt D s) (D.prob_nonneg s)
      _ = D.L * ∑ s : D.Sample, D.prob s * D.defectWeightAt s := by
            calc
              ∑ s : D.Sample, D.prob s * (D.L * D.defectWeightAt s)
                  = ∑ s : D.Sample, D.L * (D.prob s * D.defectWeightAt s) := by
                      apply Finset.sum_congr rfl
                      intro s hs
                      ring
              _ = D.L * ∑ s : D.Sample, D.prob s * D.defectWeightAt s := by
                    rw [Finset.mul_sum]
  · unfold FoldHammingLipschitzBudgetData.layerwiseDefectBudgetBound
      FoldHammingLipschitzBudgetData.expectedDefectWeight
      FoldHammingLipschitzBudgetData.expectedLayerwiseBudget
    refine Finset.sum_le_sum ?_
    intro s hs
    exact mul_le_mul_of_nonneg_left
      (defectWeightAt_le_layerwiseBudgetAt D s) (D.prob_nonneg s)

end Omega.Folding
