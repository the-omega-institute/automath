import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators fwdDiff

/-- The characteristic-`2` forward difference `a(n+1) + a(n)`. -/
def forwardDiff (a : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  Δ_[1] a

@[simp] lemma iterate_forwardDiff_eq (k : ℕ) (a : ℕ → ZMod 2) :
    Nat.iterate forwardDiff k a = Δ_[1]^[k] a := rfl

@[simp] lemma forwardDiff_zero : forwardDiff (fun _ ↦ (0 : ZMod 2)) = fun _ ↦ 0 := by
  ext n
  simp [forwardDiff]

@[simp] lemma iterate_forwardDiff_zero (k : ℕ) :
    Nat.iterate forwardDiff k (fun _ ↦ (0 : ZMod 2)) = fun _ ↦ 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, forwardDiff_zero]

/-- A tail annihilated by a high forward difference is a finite mod-`2` binomial polynomial on the
same tail. This is the shifted form needed by the conclusion chapter.
    prop:conclusion-f2-binomial-basis-from-delta-nilpotent -/
theorem paper_conclusion_f2_binomial_basis_from_delta_nilpotent
    (a : ℕ → ZMod 2) (b m0 : ℕ)
    (hnil : ∀ n ≥ m0, Nat.iterate forwardDiff b a n = 0) :
    ∃ c : Fin b → ZMod 2, ∀ n ≥ m0,
      a n = ∑ j : Fin b, c j * (Nat.choose (n - m0) j : ZMod 2) := by
  let tail : ℕ → ZMod 2 := fun n => a (m0 + n)
  have htail_zero : Nat.iterate forwardDiff b tail = fun _ ↦ 0 := by
    funext n
    have hbase : Δ_[1]^[b] a (n + m0) = 0 := by
      simpa [iterate_forwardDiff_eq, forwardDiff, add_comm] using
        hnil (n + m0) (Nat.le_add_left m0 n)
    simpa [tail, iterate_forwardDiff_eq, forwardDiff, add_assoc, add_comm, add_left_comm] using
      (fwdDiff_iter_comp_add (h := 1) (f := a) (m := m0) (n := b) (y := n)).trans hbase
  have hhigh : ∀ k, b ≤ k → Nat.iterate forwardDiff k tail 0 = 0 := by
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_comm, Function.iterate_add_apply, htail_zero, iterate_forwardDiff_zero]
  refine ⟨fun j => Nat.iterate forwardDiff j.1 tail 0, ?_⟩
  intro n hn
  let m := n - m0
  have hnm : n = m0 + m := by
    exact (Nat.add_sub_of_le hn).symm
  have hNewton :
      tail m = ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 := by
    simpa [tail, m, iterate_forwardDiff_eq, forwardDiff, nsmul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using (shift_eq_sum_fwdDiff_iter (h := 1) (f := tail) (n := m) (y := 0))
  let N := max b (m + 1)
  have hN1 : m + 1 ≤ N := by
    simp [N]
  have hNb : b ≤ N := by
    simp [N]
  have hExtendChoose :
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 =
        ∑ k ∈ Finset.range N, (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 := by
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hk) hN1
    · intro k hkN hk
      have hk' : m + 1 ≤ k := by
        exact Nat.le_of_not_lt (by simpa [Finset.mem_range] using hk)
      have hchoose : Nat.choose m k = 0 := Nat.choose_eq_zero_of_lt (lt_of_lt_of_le (Nat.lt_succ_self m) hk')
      simp [hchoose]
  have hExtendZero :
      ∑ k ∈ Finset.range b, (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 =
        ∑ k ∈ Finset.range N, (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 := by
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hk) hNb
    · intro k hkN hk
      have hk' : b ≤ k := by
        exact Nat.le_of_not_lt (by simpa [Finset.mem_range] using hk)
      simp [hhigh k hk']
  calc
    a n = tail m := by simp [tail, hnm]
    _ = ∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 := hNewton
    _ = ∑ k ∈ Finset.range N,
          (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 := hExtendChoose
    _ = ∑ k ∈ Finset.range b,
          (Nat.choose m k : ZMod 2) * Nat.iterate forwardDiff k tail 0 := hExtendZero.symm
    _ = ∑ k ∈ Finset.range b,
          Nat.iterate forwardDiff k tail 0 * (Nat.choose m k : ZMod 2) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [mul_comm]
    _ = ∑ j : Fin b, Nat.iterate forwardDiff j.1 tail 0 * (Nat.choose m j : ZMod 2) := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (f := fun k => Nat.iterate forwardDiff k tail 0 * (Nat.choose m k : ZMod 2))
              (n := b)).symm
    _ = ∑ j : Fin b, Nat.iterate forwardDiff j.1 tail 0 * (Nat.choose (n - m0) j : ZMod 2) := by
          simp [m]

end Omega.Conclusion
