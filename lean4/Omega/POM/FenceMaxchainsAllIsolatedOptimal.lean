import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Omega.POM.FenceMaxchainsEuler

namespace Omega.POM

open scoped BigOperators

lemma pom_fence_maxchains_all_isolated_optimal_eulerProduct_eq_one
    {lengths : List ℕ} (hall : ∀ n ∈ lengths, n = 1) :
    fenceEulerProduct lengths = 1 := by
  unfold fenceEulerProduct
  refine Finset.prod_eq_one ?_
  intro i hi
  have hget : lengths.get i = 1 := hall _ (List.get_mem lengths i)
  rw [fenceEulerComponentCount, if_pos hget]

lemma pom_fence_maxchains_all_isolated_optimal_eulerProduct_eq_zero
    {lengths : List ℕ} (hnot : ¬ ∀ n ∈ lengths, n = 1) :
    fenceEulerProduct lengths = 0 := by
  rw [List.forall_mem_iff_get] at hnot
  push_neg at hnot
  rcases hnot with ⟨i, hi⟩
  unfold fenceEulerProduct
  refine Finset.prod_eq_zero_iff.mpr ?_
  exact ⟨i, Finset.mem_univ i, by rw [fenceEulerComponentCount, if_neg hi]⟩

lemma pom_fence_maxchains_all_isolated_optimal_shuffle_eq_factorial
    {lengths : List ℕ} (hall : ∀ n ∈ lengths, n = 1) :
    fenceShuffleCount lengths = Nat.factorial lengths.sum := by
  unfold fenceShuffleCount
  have hspec :=
    Nat.multinomial_spec (s := (Finset.univ : Finset (Fin lengths.length)))
      (f := fun i => lengths.get i)
  have hprod :
      (∏ i ∈ (Finset.univ : Finset (Fin lengths.length)), Nat.factorial (lengths.get i)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro i hi
    have hget : lengths.get i = 1 := hall _ (List.get_mem lengths i)
    rw [hget]
    simp
  have hsum :
      (∑ i : Fin lengths.length, lengths.get i) = lengths.sum := by
    have hsumList : (List.ofFn fun i : Fin lengths.length => lengths.get i).sum = lengths.sum := by
      simpa using congrArg List.sum (List.ofFn_get lengths)
    simpa using hsumList
  rw [hprod, hsum] at hspec
  simpa [fenceShuffleCount] using hspec

/-- Paper label: `cor:pom-fence-maxchains-all-isolated-optimal`. In the chapter-local fence model,
the Euler factor is supported exactly on isolated components, so the scheduling count is bounded by
the multinomial shuffle term and reaches the factorial extremum precisely when every component has
length `1`. -/
theorem paper_pom_fence_maxchains_all_isolated_optimal (lengths : List Nat) :
    fenceMaxchainsEulerCount lengths ≤ Nat.factorial lengths.sum ∧
      (fenceMaxchainsEulerCount lengths = Nat.factorial lengths.sum ↔
        ∀ n ∈ lengths, n = 1) := by
  by_cases hall : ∀ n ∈ lengths, n = 1
  · have hprod : fenceEulerProduct lengths = 1 :=
      pom_fence_maxchains_all_isolated_optimal_eulerProduct_eq_one hall
    have hshuffle : fenceShuffleCount lengths = Nat.factorial lengths.sum :=
      pom_fence_maxchains_all_isolated_optimal_shuffle_eq_factorial hall
    have hcount : fenceMaxchainsEulerCount lengths = Nat.factorial lengths.sum := by
      simp [fenceMaxchainsEulerCount, hshuffle, hprod]
    refine ⟨hcount.le, ?_⟩
    exact ⟨fun _ => hall, fun _ => hcount⟩
  · have hprod0 : fenceEulerProduct lengths = 0 :=
      pom_fence_maxchains_all_isolated_optimal_eulerProduct_eq_zero hall
    have hcount0 : fenceMaxchainsEulerCount lengths = 0 := by
      simp [fenceMaxchainsEulerCount, hprod0]
    refine ⟨by rw [hcount0]; exact Nat.zero_le _, ?_⟩
    constructor
    · intro heq
      exfalso
      have hfac : 0 < Nat.factorial lengths.sum := Nat.factorial_pos _
      rw [hcount0] at heq
      exact (Nat.ne_of_lt hfac) heq
    · intro hall'
      exact (hall hall').elim

end Omega.POM
