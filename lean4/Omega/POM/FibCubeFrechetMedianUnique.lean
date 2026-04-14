import Omega.Folding.HammingDist
import Omega.Folding.FiberFusion
import Mathlib.Tactic

namespace Omega.POM

private theorem coord_true_filter_card_eq_coordOneCount (n : Nat) (i : Fin n) :
    (Finset.univ.filter (fun x : Omega.X n => x.1 i = true)).card = Omega.coordOneCount n i := by
  classical
  simp only [Omega.coordOneCount]
  exact Finset.card_bij (fun x _ => x.1)
    (fun x hx => by
      simp [Finset.mem_filter] at hx ⊢
      exact ⟨x.2, hx⟩)
    (fun x₁ _ x₂ _ h => Subtype.ext h)
    (fun w hw => by
      simp [Finset.mem_filter] at hw
      exact ⟨⟨w, hw.1⟩, by simp [Finset.mem_filter, hw.2], rfl⟩)

private theorem coord_false_filter_card_eq (n : Nat) (i : Fin n) :
    (Finset.univ.filter (fun x : Omega.X n => x.1 i = false)).card =
      Fintype.card (Omega.X n) - Omega.coordOneCount n i := by
  classical
  let sFalse : Finset (Omega.X n) := Finset.univ.filter (fun x : Omega.X n => x.1 i = false)
  let sTrue : Finset (Omega.X n) := Finset.univ.filter (fun x : Omega.X n => x.1 i = true)
  have hsplit : sFalse ∪ sTrue = (Finset.univ : Finset (Omega.X n)) := by
    ext x
    cases hxi : x.1 i <;> simp [sFalse, sTrue, hxi]
  have hdisj : Disjoint sFalse sTrue := by
    apply Finset.disjoint_filter.mpr
    intro x _ hxFalse hxTrue
    cases hxi : x.1 i <;> simp [hxi] at hxFalse hxTrue
  have hcard : sFalse.card + sTrue.card = Fintype.card (Omega.X n) := by
    rw [← Finset.card_univ, ← hsplit, Finset.card_union_of_disjoint hdisj]
  rw [coord_true_filter_card_eq_coordOneCount] at hcard
  exact Nat.eq_sub_of_add_eq hcard

private theorem total_hamming_cost_eq_coord_sum {n : Nat} (x : Omega.X n) :
    Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist x.1 y.1) =
      ∑ i : Fin n,
        if x.1 i = true then Fintype.card (Omega.X n) - Omega.coordOneCount n i
        else Omega.coordOneCount n i := by
  classical
  calc
    Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist x.1 y.1)
        = ∑ y : Omega.X n, ∑ i : Fin n, if x.1 i ≠ y.1 i then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Omega.hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i : Fin n, ∑ y : Omega.X n, if x.1 i ≠ y.1 i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n,
          if x.1 i = true then Fintype.card (Omega.X n) - Omega.coordOneCount n i
          else Omega.coordOneCount n i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hxi : x.1 i = true
        · calc
            (∑ y : Omega.X n, if x.1 i ≠ y.1 i then 1 else 0)
                = (∑ y : Omega.X n, if y.1 i = false then 1 else 0) := by
                    exact Finset.sum_congr rfl (fun y _ => by
                      cases hy : y.1 i <;> simp [hxi])
            _ = (Finset.univ.filter (fun y : Omega.X n => y.1 i = false)).card := by
                  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
            _ = Fintype.card (Omega.X n) - Omega.coordOneCount n i :=
                  coord_false_filter_card_eq n i
            _ = if x.1 i = true then Fintype.card (Omega.X n) - Omega.coordOneCount n i
                  else Omega.coordOneCount n i := by
                  simp [hxi]
        · have hxi' : x.1 i = false := by
            cases hbit : x.1 i <;> simp_all
          calc
            (∑ y : Omega.X n, if x.1 i ≠ y.1 i then 1 else 0)
                = (∑ y : Omega.X n, if y.1 i = true then 1 else 0) := by
                    exact Finset.sum_congr rfl (fun y _ => by
                      cases hy : y.1 i <;> simp [hxi'])
            _ = (Finset.univ.filter (fun y : Omega.X n => y.1 i = true)).card := by
                  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
            _ = Omega.coordOneCount n i := coord_true_filter_card_eq_coordOneCount n i
            _ = if x.1 i = true then Fintype.card (Omega.X n) - Omega.coordOneCount n i
                  else Omega.coordOneCount n i := by
                  simp [hxi']

private theorem double_coordOneCount_lt_card {n : Nat} (hn : 2 ≤ n) (i : Fin n) :
    2 * Omega.coordOneCount n i < Fintype.card (Omega.X n) := by
  rw [Omega.coordOneCount_eq_fib_prod, Omega.X.card_eq_fib]
  have hcoord_le : Nat.fib (i.val + 1) * Nat.fib (n - i.val) ≤ Nat.fib n := by
    have hfusion := Omega.fib_fusion (i.val + 1) (n - i.val) (by omega) (by omega)
    have hindex : i.val + 1 + (n - i.val) - 1 = n := by omega
    rw [hindex] at hfusion
    exact Nat.le.intro hfusion.symm
  have hfib_lt : 2 * Nat.fib n < Nat.fib (n + 2) := by
    have hsucc : Nat.fib n < Nat.fib (n + 1) := Nat.fib_lt_fib_succ (by omega)
    have hrec : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcoord_le) hfib_lt

private theorem total_hamming_cost_eq_zero_cost_add_penalty {n : Nat} (hn : 2 ≤ n)
    (x : Omega.X n) :
    Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist x.1 y.1) =
      (∑ i : Fin n, Omega.coordOneCount n i) +
      ∑ i : Fin n,
        if x.1 i = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i else 0 := by
  have hpoint :
      ∀ i : Fin n,
        (if x.1 i = true then Fintype.card (Omega.X n) - Omega.coordOneCount n i
         else Omega.coordOneCount n i) =
        Omega.coordOneCount n i +
          (if x.1 i = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i else 0) := by
    intro i
    by_cases hxi : x.1 i = true
    · have hle : 2 * Omega.coordOneCount n i ≤ Fintype.card (Omega.X n) := by
        exact Nat.le_of_lt (double_coordOneCount_lt_card hn i)
      simp [hxi]
      omega
    · have hxi' : x.1 i = false := by
        cases hbit : x.1 i <;> simp_all
      simp [hxi']
  calc
    Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist x.1 y.1)
        = ∑ i : Fin n,
            if x.1 i = true then Fintype.card (Omega.X n) - Omega.coordOneCount n i
            else Omega.coordOneCount n i :=
          total_hamming_cost_eq_coord_sum x
    _ = ∑ i : Fin n,
          (Omega.coordOneCount n i +
            if x.1 i = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hpoint i
    _ = (∑ i : Fin n, Omega.coordOneCount n i) +
          ∑ i : Fin n,
            if x.1 i = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i else 0 := by
          rw [Finset.sum_add_distrib]

private theorem zero_vertex_total_hamming_cost (n : Nat) :
    Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist (fun _ => false) y.1) =
      ∑ i : Fin n, Omega.coordOneCount n i := by
  simpa using
    total_hamming_cost_eq_coord_sum
      (x := (Subtype.mk (fun _ => false) Omega.no11_allFalse : Omega.X n))

set_option maxHeartbeats 400000 in
/-- The all-false Fibonacci-cube vertex is the unique Fréchet median for `n ≥ 2`.
    thm:pom-fibcube-frechet-median-unique -/
theorem paper_pom_fibcube_frechet_median_unique {n : Nat} (hn : 2 <= n) (x : Omega.X n) :
    Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist x.1 y.1) =
      Finset.univ.sum (fun y : Omega.X n => Omega.hammingDist (fun _ => false) y.1) <->
      x = Subtype.mk (fun _ => false) Omega.no11_allFalse := by
  let zeroX : Omega.X n := Subtype.mk (fun _ => false) Omega.no11_allFalse
  constructor
  · intro hEq
    by_cases hzero : x = zeroX
    · exact hzero
    · have hsumx := total_hamming_cost_eq_zero_cost_add_penalty hn x
      have hsum0 := zero_vertex_total_hamming_cost n
      have hpenalty_zero :
          (∑ i : Fin n,
            if x.1 i = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i else 0) = 0 := by
        rw [hsumx, hsum0] at hEq
        omega
      have hpop_ne : Omega.popcount x.1 ≠ 0 := by
        intro hpop
        exact hzero ((Omega.popcount_eq_zero_iff x).mp hpop)
      have hsupport : (Omega.wordSupport x.1).Nonempty := by
        simpa [Omega.popcount] using Nat.pos_of_ne_zero hpop_ne
      rcases hsupport with ⟨i, hi⟩
      have hxi : x.1 i = true := by
        simp [Omega.wordSupport, Finset.mem_filter] at hi
        exact hi
      have hdelta_pos : 0 < Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i := by
        exact Nat.sub_pos_of_lt (double_coordOneCount_lt_card hn i)
      have hdelta_le :
          Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n i ≤
            (∑ j : Fin n,
              if x.1 j = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n j else 0) := by
        have hsingle :=
          Finset.single_le_sum
            (f := fun j : Fin n =>
              if x.1 j = true then Fintype.card (Omega.X n) - 2 * Omega.coordOneCount n j else 0)
            (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
        simpa [hxi] using hsingle
      omega
  · intro hx
    subst hx
    simp

end Omega.POM
