import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite data for the partition-pressure knapsack comparison. `P r` is the pressure
attached to a part of size `r`, `bestPart` realizes the maximal normalized slope, and `P 0 = 0`
keeps the zero slot neutral while the actual budget constraints live on part sizes `1, …, q`. -/
structure PartitionPressureKnapsackData where
  q : ℕ
  hq : 1 ≤ q
  P : ℕ → ℚ
  P_zero : P 0 = 0
  bestPart : ℕ
  bestPart_pos : 1 ≤ bestPart
  bestPart_le : bestPart ≤ q
  bestPart_optimal :
    ∀ r : ℕ, 1 ≤ r → r ≤ q → P r / r ≤ P bestPart / bestPart

namespace PartitionPressureKnapsackData

def optimalSlope (D : PartitionPressureKnapsackData) : ℚ :=
  D.P D.bestPart / D.bestPart

def totalSize (D : PartitionPressureKnapsackData) (c : Fin (D.q + 1) → ℕ) : ℕ :=
  ∑ r : Fin (D.q + 1), (r : ℕ) * c r

def partitionPressure (D : PartitionPressureKnapsackData) (c : Fin (D.q + 1) → ℕ) : ℚ :=
  ∑ r : Fin (D.q + 1), (c r : ℚ) * D.P r

/-- Feasible multiplicity vectors use no zero-sized parts and spend the full budget `q`. -/
def respectsBudget (D : PartitionPressureKnapsackData) (c : Fin (D.q + 1) → ℕ) : Prop :=
  c 0 = 0 ∧ D.totalSize c = D.q

def partIsOptimal (D : PartitionPressureKnapsackData) (r : Fin (D.q + 1)) : Prop :=
  1 ≤ (r : ℕ) ∧ D.P r / (r : ℚ) = D.optimalSlope

def singleBestPartCounts (D : PartitionPressureKnapsackData) : Fin (D.q + 1) → ℕ :=
  fun r => if (r : ℕ) = D.bestPart then D.q / D.bestPart else 0

def pressureUpperBound (D : PartitionPressureKnapsackData) : Prop :=
  ∀ c : Fin (D.q + 1) → ℕ, D.respectsBudget c →
    D.partitionPressure c ≤ (D.q : ℚ) * D.optimalSlope

def maximizersUseOnlyOptimalParts (D : PartitionPressureKnapsackData) : Prop :=
  ∀ c : Fin (D.q + 1) → ℕ, D.respectsBudget c →
    D.partitionPressure c = (D.q : ℚ) * D.optimalSlope →
      ∀ r : Fin (D.q + 1), 0 < c r → 1 ≤ (r : ℕ) → D.partIsOptimal r

def uniqueMaximizerOfSingleBestPart (D : PartitionPressureKnapsackData) : Prop :=
  ((∀ r : Fin (D.q + 1), 1 ≤ (r : ℕ) → D.partIsOptimal r → (r : ℕ) = D.bestPart) ∧
      D.bestPart ∣ D.q) →
    D.respectsBudget D.singleBestPartCounts ∧
      D.partitionPressure D.singleBestPartCounts = (D.q : ℚ) * D.optimalSlope ∧
      ∀ c : Fin (D.q + 1) → ℕ, D.respectsBudget c →
        D.partitionPressure c = (D.q : ℚ) * D.optimalSlope →
          c = D.singleBestPartCounts

lemma bestPart_ne_zero (D : PartitionPressureKnapsackData) : D.bestPart ≠ 0 := by
  exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one D.bestPart_pos)

lemma part_pressure_le (D : PartitionPressureKnapsackData) (r : Fin (D.q + 1)) :
    D.P r ≤ (r : ℚ) * D.optimalSlope := by
  by_cases hr0 : (r : ℕ) = 0
  · have hre : r = 0 := Fin.ext hr0
    subst hre
    simp [optimalSlope, D.P_zero]
  · have hr_pos_nat : 1 ≤ (r : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)
    have hr_le : (r : ℕ) ≤ D.q := Nat.le_of_lt_succ r.2
    have hratio := D.bestPart_optimal r hr_pos_nat hr_le
    have hr_pos_rat : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
    have := (div_le_iff₀ hr_pos_rat).1 hratio
    simpa [optimalSlope, mul_comm, mul_left_comm, mul_assoc] using this

lemma weighted_part_pressure_le (D : PartitionPressureKnapsackData) (c : Fin (D.q + 1) → ℕ)
    (r : Fin (D.q + 1)) :
    (c r : ℚ) * D.P r ≤ ((r : ℚ) * (c r : ℚ)) * D.optimalSlope := by
  have hcoeff : 0 ≤ (c r : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (D.part_pressure_le r) hcoeff
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

lemma partitionPressure_le_weightedSum (D : PartitionPressureKnapsackData) (c : Fin (D.q + 1) → ℕ) :
    D.partitionPressure c ≤
      ∑ r : Fin (D.q + 1), ((r : ℚ) * (c r : ℚ)) * D.optimalSlope := by
  exact Finset.sum_le_sum fun r _ => D.weighted_part_pressure_le c r

lemma weightedSum_eq_budget_mul (D : PartitionPressureKnapsackData) (c : Fin (D.q + 1) → ℕ)
    (hc : D.respectsBudget c) :
    (∑ r : Fin (D.q + 1), ((r : ℚ) * (c r : ℚ)) * D.optimalSlope) =
      (D.q : ℚ) * D.optimalSlope := by
  have hcast :
      ∑ r : Fin (D.q + 1), ((r : ℚ) * (c r : ℚ)) =
        ((∑ r : Fin (D.q + 1), (r : ℕ) * c r : ℕ) : ℚ) := by
    norm_num [Nat.cast_sum, Nat.cast_mul]
  calc
    (∑ r : Fin (D.q + 1), ((r : ℚ) * (c r : ℚ)) * D.optimalSlope)
        = (∑ r : Fin (D.q + 1), ((r : ℚ) * (c r : ℚ))) * D.optimalSlope := by
            rw [Finset.sum_mul]
    _ = ((∑ r : Fin (D.q + 1), (r : ℕ) * c r : ℕ) : ℚ) * D.optimalSlope := by rw [hcast]
    _ = (D.q : ℚ) * D.optimalSlope := by
          have hbudgetQ : (((∑ r : Fin (D.q + 1), (r : ℕ) * c r : ℕ) : ℚ)) = (D.q : ℚ) := by
            exact_mod_cast hc.2
          rw [hbudgetQ]

lemma part_pressure_lt_of_nonoptimal (D : PartitionPressureKnapsackData) (r : Fin (D.q + 1))
    (hr : 1 ≤ (r : ℕ)) (hnot : ¬ D.partIsOptimal r) :
    D.P r < (r : ℚ) * D.optimalSlope := by
  have hle := D.part_pressure_le r
  have hneq : D.P r ≠ (r : ℚ) * D.optimalSlope := by
    intro heq
    apply hnot
    refine ⟨hr, ?_⟩
    have hr_pos_rat : (0 : ℚ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
    apply (div_eq_iff hr_pos_rat.ne').2
    simpa [optimalSlope, mul_comm, mul_left_comm, mul_assoc] using heq
  exact lt_of_le_of_ne hle hneq

lemma weighted_part_pressure_lt_of_nonoptimal (D : PartitionPressureKnapsackData)
    (c : Fin (D.q + 1) → ℕ) (r : Fin (D.q + 1))
    (hcpos : 0 < c r) (hr : 1 ≤ (r : ℕ)) (hnot : ¬ D.partIsOptimal r) :
    (c r : ℚ) * D.P r < ((r : ℚ) * (c r : ℚ)) * D.optimalSlope := by
  have hlt := D.part_pressure_lt_of_nonoptimal r hr hnot
  have hcoeff : (0 : ℚ) < c r := by exact_mod_cast hcpos
  have hmul := mul_lt_mul_of_pos_left hlt hcoeff
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

lemma singleBestPartCounts_respectsBudget (D : PartitionPressureKnapsackData)
    (hdiv : D.bestPart ∣ D.q) :
    D.respectsBudget D.singleBestPartCounts := by
  have hbest_mem : D.bestPart < D.q + 1 := Nat.lt_succ_of_le D.bestPart_le
  let rbest : Fin (D.q + 1) := ⟨D.bestPart, hbest_mem⟩
  have hsum :
      ∑ r : Fin (D.q + 1), (r : ℕ) * D.singleBestPartCounts r =
        D.bestPart * (D.q / D.bestPart) := by
    classical
    calc
      ∑ r : Fin (D.q + 1), (r : ℕ) * D.singleBestPartCounts r =
          (rbest : ℕ) * D.singleBestPartCounts rbest := by
            apply Finset.sum_eq_single rbest
            · intro r _ hr
              by_cases hrbest : (r : ℕ) = D.bestPart
              · exfalso
                apply hr
                exact Fin.ext hrbest
              · simp [singleBestPartCounts, hrbest]
            · simp [singleBestPartCounts]
      _ = D.bestPart * (D.q / D.bestPart) := by
            simp [rbest, singleBestPartCounts]
  refine ⟨?_, ?_⟩
  · dsimp [singleBestPartCounts]
    exact if_neg (by simpa using D.bestPart_ne_zero.symm)
  · dsimp [totalSize]
    rw [hsum]
    exact Nat.mul_div_cancel' hdiv

lemma singleBestPartCounts_pressure (D : PartitionPressureKnapsackData) (hdiv : D.bestPart ∣ D.q) :
    D.partitionPressure D.singleBestPartCounts = (D.q : ℚ) * D.optimalSlope := by
  rcases hdiv with ⟨k, hk⟩
  have hbest_mem : D.bestPart < D.q + 1 := Nat.lt_succ_of_le D.bestPart_le
  let rbest : Fin (D.q + 1) := ⟨D.bestPart, hbest_mem⟩
  have hsum :
      D.partitionPressure D.singleBestPartCounts =
        ((D.q / D.bestPart : ℕ) : ℚ) * D.P D.bestPart := by
    classical
    dsimp [partitionPressure]
    calc
      ∑ r : Fin (D.q + 1), (D.singleBestPartCounts r : ℚ) * D.P r =
          (D.singleBestPartCounts rbest : ℚ) * D.P rbest := by
            apply Finset.sum_eq_single rbest
            · intro r _ hr
              by_cases hrbest : (r : ℕ) = D.bestPart
              · exfalso
                apply hr
                exact Fin.ext hrbest
              · simp [singleBestPartCounts, hrbest]
            · simp [singleBestPartCounts]
      _ = ((D.q / D.bestPart : ℕ) : ℚ) * D.P D.bestPart := by
            simp [rbest, singleBestPartCounts]
  have hkdiv : D.q / D.bestPart = k := by
    have hbest_pos : 0 < D.bestPart := lt_of_lt_of_le Nat.zero_lt_one D.bestPart_pos
    rw [hk]
    simpa [Nat.mul_comm] using (Nat.mul_div_right k hbest_pos)
  have hbp : (D.bestPart : ℚ) ≠ 0 := by
    exact_mod_cast D.bestPart_ne_zero
  have hbest_eq : D.P D.bestPart = (D.bestPart : ℚ) * D.optimalSlope := by
    rw [optimalSlope]
    field_simp [hbp]
  calc
    D.partitionPressure D.singleBestPartCounts
        = (k : ℚ) * D.P D.bestPart := by simpa [hkdiv] using hsum
    _ = (k : ℚ) * ((D.bestPart : ℚ) * D.optimalSlope) := by rw [hbest_eq]
    _ = ((D.bestPart * k : ℕ) : ℚ) * D.optimalSlope := by
          norm_num [mul_assoc, mul_left_comm, mul_comm]
    _ = (D.q : ℚ) * D.optimalSlope := by rw [hk]

end PartitionPressureKnapsackData

open PartitionPressureKnapsackData

/-- Comparing each used part against the maximal normalized slope gives the knapsack upper bound;
equality forces every used part to have optimal slope; and when a single best part divides the
budget, the pure `r_*` partition is the unique maximizer at the upper-bound value.
    prop:pom-partition-pressure-knapsack -/
theorem paper_pom_partition_pressure_knapsack (D : PartitionPressureKnapsackData) :
    D.pressureUpperBound ∧ D.maximizersUseOnlyOptimalParts ∧ D.uniqueMaximizerOfSingleBestPart := by
  have hupper : D.pressureUpperBound := by
    intro c hc
    calc
      D.partitionPressure c ≤ ∑ r : Fin (D.q + 1), ((r : ℚ) * (c r : ℚ)) * D.optimalSlope :=
        D.partitionPressure_le_weightedSum c
      _ = (D.q : ℚ) * D.optimalSlope := D.weightedSum_eq_budget_mul c hc
  have hmaxUse : D.maximizersUseOnlyOptimalParts := by
    intro c hc hmax r hcpos hr
    refine ⟨hr, ?_⟩
    by_contra hnot_eq
    have hnot : ¬ D.partIsOptimal r := by
      intro hopt
      exact hnot_eq hopt.2
    let f : Fin (D.q + 1) → ℚ := fun s => (c s : ℚ) * D.P s
    let g : Fin (D.q + 1) → ℚ := fun s => ((s : ℚ) * (c s : ℚ)) * D.optimalSlope
    have hle : ∀ s ∈ (Finset.univ : Finset (Fin (D.q + 1))), f s ≤ g s := by
      intro s _
      exact D.weighted_part_pressure_le c s
    have hlt : ∃ s ∈ (Finset.univ : Finset (Fin (D.q + 1))), f s < g s := by
      refine ⟨r, Finset.mem_univ _, ?_⟩
      exact D.weighted_part_pressure_lt_of_nonoptimal c r hcpos hr hnot
    have hsumlt : ∑ s : Fin (D.q + 1), f s < ∑ s : Fin (D.q + 1), g s := by
      simpa [f, g] using Finset.sum_lt_sum hle hlt
    have hupperEq : ∑ s : Fin (D.q + 1), g s = (D.q : ℚ) * D.optimalSlope :=
      D.weightedSum_eq_budget_mul c hc
    have hstrict : D.partitionPressure c < (D.q : ℚ) * D.optimalSlope := by
      simpa [partitionPressure, f, g] using hsumlt.trans_eq hupperEq
    exact absurd (hmax ▸ hstrict) (lt_irrefl _)
  refine ⟨hupper, hmaxUse, ?_⟩
  intro hsingle
  rcases hsingle with ⟨huniq, hdiv⟩
  refine ⟨D.singleBestPartCounts_respectsBudget hdiv, D.singleBestPartCounts_pressure hdiv, ?_⟩
  intro c hc hmax
  funext r
  by_cases hrbest : (r : ℕ) = D.bestPart
  · have hsupportZero : ∀ s : Fin (D.q + 1), s ≠ r → c s = 0 := by
      intro s hsr
      by_contra hsne
      have hsposCount : 0 < c s := Nat.pos_of_ne_zero hsne
      have hs_nat_ne_zero : (s : ℕ) ≠ 0 := by
        intro hs0
        have hse : s = 0 := Fin.ext hs0
        have : c s = 0 := by simpa [hse] using hc.1
        exact hsne this
      have hspos : 1 ≤ (s : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs_nat_ne_zero)
      have hsopt := hmaxUse c hc hmax s hsposCount hspos
      have hsbest : (s : ℕ) = D.bestPart := huniq s hspos hsopt
      exact hsr (Fin.ext (hsbest.trans hrbest.symm))
    have hsum : D.bestPart * c r = D.totalSize c := by
      classical
      dsimp [totalSize]
      calc
        D.bestPart * c r = (r : ℕ) * c r := by simp [hrbest]
        _ = ∑ s : Fin (D.q + 1), (s : ℕ) * c s := by
              symm
              apply Finset.sum_eq_single r
              · intro s _ hsr
                simp [hsupportZero s hsr]
              · simp
    have hmul : D.bestPart * c r = D.q := hsum.trans hc.2
    have hcount : c r = D.q / D.bestPart := by
      have hbest_pos : 0 < D.bestPart := lt_of_lt_of_le Nat.zero_lt_one D.bestPart_pos
      calc
        c r = (D.bestPart * c r) / D.bestPart := by
              simpa [Nat.mul_comm] using (Nat.mul_div_right (c r) hbest_pos).symm
        _ = D.q / D.bestPart := by rw [hmul]
    simp [singleBestPartCounts, hrbest, hcount]
  · have hzero : c r = 0 := by
      by_contra hne
      have hcpos : 0 < c r := Nat.pos_of_ne_zero hne
      have hr_nat_ne_zero : (r : ℕ) ≠ 0 := by
        intro hr0
        have hre : r = 0 := Fin.ext hr0
        have : c r = 0 := by simpa [hre] using hc.1
        exact hne this
      have hrpos : 1 ≤ (r : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr_nat_ne_zero)
      have hopt := hmaxUse c hc hmax r hcpos hrpos
      exact hrbest (huniq r hrpos hopt)
    simp [singleBestPartCounts, hrbest, hzero]

end Omega.POM
