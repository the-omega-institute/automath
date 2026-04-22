import Mathlib.Tactic
import Omega.Conclusion.BalancedExternalizationSchurOptimality

open scoped BigOperators

namespace Omega.Conclusion

def conclusion_balanced_externalization_optimal_renyi_energy_statement {α : Type*}
    [DecidableEq α] (X : Finset α) (d : α → ℕ) (B q : ℕ) : Prop :=
  let bucketCount := 2 ^ B
  Finset.sum X (fun x =>
      let a := d x / bucketCount
      let r := d x % bucketCount
      r * (a + 1) ^ q + (bucketCount - r) * a ^ q) ≤
    Finset.sum X (fun x => d x ^ q)

private lemma conclusion_balanced_externalization_optimal_renyi_energy_add_pow_lt_of_pos
    {a b q : Nat} (ha : 0 < a) (hb : 0 < b) (hq : 2 ≤ q) : a ^ q + b ^ q < (a + b) ^ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction n with
  | zero =>
      have hab : 0 < a * b + b * a := by
        exact lt_of_lt_of_le (Nat.mul_pos ha hb) (Nat.le_add_right (a * b) (b * a))
      calc
        a ^ 2 + b ^ 2 < a ^ 2 + b ^ 2 + (a * b + b * a) := Nat.lt_add_of_pos_right hab
        _ = (a + b) ^ 2 := by ring
  | succ n ih =>
      have hsum_pos : 0 < a + b := lt_of_lt_of_le ha (Nat.le_add_right a b)
      have ih' : a ^ (n + 2) + b ^ (n + 2) < (a + b) ^ (n + 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (by omega)
      have hleft : a ^ (n + 2) * a < a ^ (n + 2) * (a + b) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_add_of_pos_right hb) (pow_pos ha _)
      have hright : b ^ (n + 2) * b < b ^ (n + 2) * (a + b) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_add_of_pos_left ha) (pow_pos hb _)
      have hmiddle :
          a ^ (n + 2) * (a + b) + b ^ (n + 2) * (a + b) < (a + b) ^ (n + 2) * (a + b) := by
        simpa [Nat.add_mul, add_comm, add_left_comm, add_assoc] using
          (Nat.mul_lt_mul_of_pos_right ih' hsum_pos)
      calc
        a ^ (2 + (n + 1)) + b ^ (2 + (n + 1)) = a ^ (n + 2) * a + b ^ (n + 2) * b := by
          simp [pow_succ, Nat.add_assoc, Nat.add_comm, Nat.mul_comm]
        _ < a ^ (n + 2) * (a + b) + b ^ (n + 2) * (a + b) := add_lt_add hleft hright
        _ < (a + b) ^ (n + 2) * (a + b) := hmiddle
        _ = (a + b) ^ (2 + (n + 1)) := by
          simp [pow_succ, Nat.add_assoc, Nat.add_comm, Nat.mul_comm]

private lemma conclusion_balanced_externalization_optimal_renyi_energy_add_pow_le
    {a b q : Nat} (hq : 1 ≤ q) : a ^ q + b ^ q ≤ (a + b) ^ q := by
  have hq0 : q ≠ 0 := by omega
  by_cases hq1 : q = 1
  · subst hq1
    simp
  have hq2 : 2 ≤ q := by omega
  by_cases ha : a = 0
  · simp [ha, hq0]
  by_cases hb : b = 0
  · simp [hb, hq0]
  exact Nat.le_of_lt
    (conclusion_balanced_externalization_optimal_renyi_energy_add_pow_lt_of_pos
      (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hq2)

private lemma conclusion_balanced_externalization_optimal_renyi_energy_sum_pow_le_pow_sum_finset
    {ι : Type*} {q : Nat} (s : Finset ι) (a : ι → Nat) (hq : 1 ≤ q) :
    s.sum (fun i => a i ^ q) ≤ (s.sum fun i => a i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      calc
        (insert i s).sum (fun j => a j ^ q) = a i ^ q + s.sum (fun j => a j ^ q) := by simp [hi]
        _ ≤ a i ^ q + (s.sum fun j => a j) ^ q := Nat.add_le_add_left ih _
        _ ≤ (a i + s.sum (fun j => a j)) ^ q := by
          exact conclusion_balanced_externalization_optimal_renyi_energy_add_pow_le hq
        _ = ((insert i s).sum fun j => a j) ^ q := by simp [hi]

private lemma conclusion_balanced_externalization_optimal_renyi_energy_sum_indicator_range
    (N r : ℕ) (hr : r ≤ N) :
    Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0) = r := by
  calc
    Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0)
        = Finset.sum ((Finset.range N).filter (fun i => i < r)) (fun _ => 1) := by
            rw [Finset.sum_filter]
    _ = ((Finset.range N).filter (fun i => i < r)).card := by
          rw [Finset.card_eq_sum_ones]
    _ = (Finset.range r).card := by
          have hEq : (Finset.range N).filter (fun i => i < r) = Finset.range r := by
            ext i
            constructor
            · intro hi
              exact Finset.mem_range.mpr ((Finset.mem_filter.mp hi).2)
            · intro hi
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hr),
                  Finset.mem_range.mp hi⟩
          rw [hEq]
    _ = r := by simp

private lemma conclusion_balanced_externalization_optimal_renyi_energy_sum_if_lt_const
    (N r c : ℕ) (hr : r ≤ N) :
    Finset.sum (Finset.range N) (fun i => if i < r then c else 0) = r * c := by
  calc
    Finset.sum (Finset.range N) (fun i => if i < r then c else 0)
        = Finset.sum ((Finset.range N).filter (fun i => i < r)) (fun _ => c) := by
            rw [Finset.sum_filter]
    _ = ((Finset.range N).filter (fun i => i < r)).card * c := by simp
    _ = (Finset.range r).card * c := by
          have hEq : (Finset.range N).filter (fun i => i < r) = Finset.range r := by
            ext i
            constructor
            · intro hi
              exact Finset.mem_range.mpr ((Finset.mem_filter.mp hi).2)
            · intro hi
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hr),
                  Finset.mem_range.mp hi⟩
          rw [hEq]
    _ = r * c := by simp

private lemma conclusion_balanced_externalization_optimal_renyi_energy_sum_if_not_lt_const
    (N r c : ℕ) :
    Finset.sum (Finset.range N) (fun i => if i < r then 0 else c) = (N - r) * c := by
  have hrewrite :
      Finset.sum (Finset.range N) (fun i => if i < r then 0 else c) =
        Finset.sum (Finset.range N) (fun i => if ¬ i < r then c else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hir : i < r <;> simp [hir]
  rw [hrewrite]
  calc
    Finset.sum (Finset.range N) (fun i => if ¬ i < r then c else 0)
        = Finset.sum ((Finset.range N).filter (fun i => ¬ i < r)) (fun _ => c) := by
            rw [Finset.sum_filter]
    _ = ((Finset.range N).filter (fun i => ¬ i < r)).card * c := by simp
    _ = (Finset.Ico r N).card * c := by
          have hEq : (Finset.range N).filter (fun i => ¬ i < r) = Finset.Ico r N := by
            ext i
            constructor
            · intro hi
              rcases Finset.mem_filter.mp hi with ⟨hiN, hir⟩
              exact Finset.mem_Ico.mpr ⟨le_of_not_gt hir, Finset.mem_range.mp hiN⟩
            · intro hi
              rcases Finset.mem_Ico.mp hi with ⟨hir, hiN⟩
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiN, not_lt.mpr hir⟩
          rw [hEq]
    _ = (N - r) * c := by simp

private lemma conclusion_balanced_externalization_optimal_renyi_energy_balanced_sum
    (bucketCount d : ℕ) (hbucketCount : 0 < bucketCount) :
    ∑ i : Fin bucketCount, Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i = d := by
  let a := d / bucketCount
  let r := d % bucketCount
  have hr : r ≤ bucketCount := by
    exact le_of_lt (Nat.mod_lt _ hbucketCount)
  have hcount : Finset.sum (Finset.range bucketCount) (fun i => if i < r then 1 else 0) = r := by
    exact conclusion_balanced_externalization_optimal_renyi_energy_sum_indicator_range
      bucketCount r hr
  calc
    ∑ i, Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i
        = ∑ i : Fin bucketCount, (a + if i.1 < r then 1 else 0) := by
            simp [Omega.Zeta.xiTimePart64baBalancedProfile, a, r]
    _ = (∑ i : Fin bucketCount, a) + ∑ i : Fin bucketCount, (if i.1 < r then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = bucketCount * a + r := by
          have hsumInd :
              (∑ i : Fin bucketCount, (if i.1 < r then 1 else 0)) = r := by
            exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < r then 1 else 0) bucketCount).trans
              hcount
          rw [hsumInd]
          simp
    _ = d := by
          exact Nat.div_add_mod d bucketCount

private lemma conclusion_balanced_externalization_optimal_renyi_energy_pointwise_expansion
    (d B q : ℕ) :
    let bucketCount := 2 ^ B
    let a := d / bucketCount
    let r := d % bucketCount
    (∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q) =
      r * (a + 1) ^ q + (bucketCount - r) * a ^ q := by
  let bucketCount := 2 ^ B
  let a := d / bucketCount
  let r := d % bucketCount
  have hbucketCount : 0 < bucketCount := by
    simp [bucketCount]
  have hr : r ≤ bucketCount := by
    exact le_of_lt (Nat.mod_lt _ hbucketCount)
  have hsplit :
      (∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q) =
        ∑ i : Fin bucketCount, if i.1 < r then (a + 1) ^ q else a ^ q := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hir : i.1 < r <;> simp [Omega.Zeta.xiTimePart64baBalancedProfile, a, r, hir]
  have hmain :
      (∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q) =
        r * (a + 1) ^ q + (bucketCount - r) * a ^ q := by
    calc
      ∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q
          = ∑ i : Fin bucketCount, if i.1 < r then (a + 1) ^ q else a ^ q := hsplit
      _ = ∑ i : Fin bucketCount, ((if i.1 < r then (a + 1) ^ q else 0) +
            (if i.1 < r then 0 else a ^ q)) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hir : i.1 < r <;> simp [hir]
      _ = (∑ i : Fin bucketCount, if i.1 < r then (a + 1) ^ q else 0) +
            ∑ i : Fin bucketCount, (if i.1 < r then 0 else a ^ q) := by
              rw [Finset.sum_add_distrib]
      _ = r * (a + 1) ^ q + (bucketCount - r) * a ^ q := by
            have hleft :
                (∑ i : Fin bucketCount, if i.1 < r then (a + 1) ^ q else 0) = r * (a + 1) ^ q := by
              exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < r then (a + 1) ^ q else 0)
                bucketCount).trans
                (conclusion_balanced_externalization_optimal_renyi_energy_sum_if_lt_const
                  bucketCount r ((a + 1) ^ q) hr)
            have hright :
                (∑ i : Fin bucketCount, if i.1 < r then 0 else a ^ q) =
                (bucketCount - r) * a ^ q := by
              exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < r then 0 else a ^ q)
                bucketCount).trans
                (conclusion_balanced_externalization_optimal_renyi_energy_sum_if_not_lt_const
                  bucketCount r (a ^ q))
            rw [hleft, hright]
  simpa [bucketCount, a, r] using hmain

private lemma conclusion_balanced_externalization_optimal_renyi_energy_pointwise_bound
    (d B q : ℕ) (hq : 1 ≤ q) :
    let bucketCount := 2 ^ B
    let a := d / bucketCount
    let r := d % bucketCount
    r * (a + 1) ^ q + (bucketCount - r) * a ^ q ≤ d ^ q := by
  let bucketCount := 2 ^ B
  have hbucketCount : 0 < bucketCount := by
    simp [bucketCount]
  have hmain :
      ∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q ≤ d ^ q := by
    calc
      ∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q
          ≤ (∑ i : Fin bucketCount, Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q := by
              exact
                conclusion_balanced_externalization_optimal_renyi_energy_sum_pow_le_pow_sum_finset
                  (Finset.univ : Finset (Fin bucketCount))
                  (fun i => Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) hq
      _ = d ^ q := by
            rw [conclusion_balanced_externalization_optimal_renyi_energy_balanced_sum
              bucketCount d hbucketCount]
  have hexpand :
      let a := d / bucketCount
      let r := d % bucketCount
      r * (a + 1) ^ q + (bucketCount - r) * a ^ q =
        ∑ i : Fin bucketCount, (Omega.Zeta.xiTimePart64baBalancedProfile bucketCount d i) ^ q := by
    simpa [bucketCount] using
      (conclusion_balanced_externalization_optimal_renyi_energy_pointwise_expansion d B q).symm
  have hbound :
      (let a := d / bucketCount
       let r := d % bucketCount
       r * (a + 1) ^ q + (bucketCount - r) * a ^ q) ≤ d ^ q := by
    rw [hexpand]
    exact hmain
  simpa [bucketCount] using hbound

theorem paper_conclusion_balanced_externalization_optimal_renyi_energy {α : Type*}
    [DecidableEq α] (X : Finset α) (d : α → ℕ) (B q : ℕ) (hq : 1 ≤ q) :
    conclusion_balanced_externalization_optimal_renyi_energy_statement X d B q := by
  unfold conclusion_balanced_externalization_optimal_renyi_energy_statement
  apply Finset.sum_le_sum
  intro x hx
  simpa using
    conclusion_balanced_externalization_optimal_renyi_energy_pointwise_bound (d x) B q hq

end Omega.Conclusion
