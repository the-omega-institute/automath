import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Folding

/-- The Fibonacci Godel radius of a finite support set, using the shifted weights `F_{i+2}` so that
the paper's support family becomes a finite powerset over the first `k` coordinates. -/
def fibGodelRadius (I : Finset Nat) : Nat :=
  ∑ i ∈ I, Nat.fib (i + 2)

/-- The finite support family counted by the Fibonacci Godel radius bound. Any admissible support
is contained in `range (R + 1)`, so the family is realized as a filtered powerset. -/
def fibGodelRadiusFamily (R : Nat) : Finset (Finset Nat) :=
  ((Finset.range (R + 1)).powerset).filter fun I => fibGodelRadius I <= R

private lemma fibGodelRadius_single_le (I : Finset Nat) {i : Nat} (hi : i ∈ I) :
    Nat.fib (i + 2) <= fibGodelRadius I := by
  unfold fibGodelRadius
  simpa using
    (Finset.single_le_sum (f := fun j => Nat.fib (j + 2)) (fun j _ => Nat.zero_le _) hi)

private lemma fibGodelRadius_range (n : Nat) :
    fibGodelRadius (Finset.range n) = Nat.fib (n + 3) - 2 := by
  simpa [fibGodelRadius] using (Omega.fib_partial_sum_from_two n)

private lemma fibGodelRadius_range_pred (k : Nat) :
    fibGodelRadius (Finset.range (k - 2)) = Nat.fib (k + 1) - 2 := by
  cases k with
  | zero =>
      simp [fibGodelRadius]
  | succ k =>
      cases k with
      | zero =>
          simp [fibGodelRadius]
      | succ k =>
          simp [fibGodelRadius_range]

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:fold-hypercube-fibonacci-godel-radius-count`.
If `F_{k+1} <= R < F_{k+2}`, then the admissible finite-support family for the Fibonacci Godel
radius has cardinality between `2^(k-2)` and `2^k`. -/
theorem paper_fold_hypercube_fibonacci_godel_radius_count (R k : Nat)
    (hk : Nat.fib (k + 1) <= R /\ R < Nat.fib (k + 2)) :
    2 ^ (k - 2) <= (fibGodelRadiusFamily R).card /\ (fibGodelRadiusFamily R).card <= 2 ^ k := by
  rcases hk with ⟨hk_lower, hk_upper⟩
  have hk_range : k - 2 <= R + 1 := by
    have hk1 : k + 1 <= Nat.fib (k + 1) + 1 := Nat.le_fib_add_one (k + 1)
    omega
  have hupper_subset : fibGodelRadiusFamily R ⊆ (Finset.range k).powerset := by
    intro I hI
    rw [fibGodelRadiusFamily, Finset.mem_filter] at hI
    rcases hI with ⟨_, hI⟩
    rw [Finset.mem_powerset]
    intro i hi
    by_contra hik
    rw [Finset.mem_range] at hik
    have hki : k <= i := by omega
    have hmono : Nat.fib (k + 2) <= Nat.fib (i + 2) := Nat.fib_mono (by omega)
    have hweight : Nat.fib (i + 2) <= fibGodelRadius I := fibGodelRadius_single_le I hi
    have : Nat.fib (k + 2) <= R := hmono.trans (hweight.trans hI)
    omega
  have hlower_subset : (Finset.range (k - 2)).powerset ⊆ fibGodelRadiusFamily R := by
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    rw [fibGodelRadiusFamily, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact hJ.trans (Finset.range_subset_range.mpr hk_range)
    · have hsum :
          fibGodelRadius J <= fibGodelRadius (Finset.range (k - 2)) := by
        unfold fibGodelRadius
        exact Finset.sum_le_sum_of_subset_of_nonneg hJ (fun _ _ _ => Nat.zero_le _)
      calc
        fibGodelRadius J <= fibGodelRadius (Finset.range (k - 2)) := hsum
        _ = Nat.fib (k + 1) - 2 := by
              simpa using fibGodelRadius_range_pred k
        _ <= Nat.fib (k + 1) := Nat.sub_le _ _
        _ <= R := hk_lower
  refine ⟨?_, ?_⟩
  · simpa using Finset.card_le_card hlower_subset
  · simpa using Finset.card_le_card hupper_subset

end Omega.Folding
