import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-monotone-idempotent-skeleton-superexponential-sparsity`. -/
theorem paper_xi_monotone_idempotent_skeleton_superexponential_sparsity (n : Nat)
    (hn : 2 <= n) :
    ((2 : Real) ^ (n - 1)) /
        ((Finset.Icc 1 n).sum
          (fun k => (Nat.choose n k : Real) * (k : Real) ^ (n - k))) <=
      ((n + 1 : Nat) : Real) /
        (2 * ((n / 2 : Nat) : Real) ^ (n - n / 2)) := by
  let m := n / 2
  let S : Real :=
    (Finset.Icc 1 n).sum (fun k => (Nat.choose n k : Real) * (k : Real) ^ (n - k))
  let M : Real := (m : Real) ^ (n - m)
  have hn_pos : 0 < n := by omega
  have hm_nat_pos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos hn (by norm_num)
  have hm_pos : 0 < (m : Real) := by exact_mod_cast hm_nat_pos
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  have hB_pos : 0 < ((n + 1 : Nat) : Real) := by positivity
  have hm_mem : m ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    exact ⟨hm_nat_pos, Nat.div_le_self n 2⟩
  have hsum_ge :
      (Nat.choose n m : Real) * M <= S := by
    dsimp [S, M]
    refine Finset.single_le_sum (s := Finset.Icc 1 n) (a := m)
      (f := fun k => (Nat.choose n k : Real) * (k : Real) ^ (n - k)) ?_ hm_mem
    intro k _hk
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (Nat.choose n k)) (by positivity)
  have hchoose_lower_nat : 2 ^ n <= (n + 1) * Nat.choose n m := by
    calc
      2 ^ n = (Finset.range (n + 1)).sum (fun k => Nat.choose n k) := by
        rw [Nat.sum_range_choose]
      _ <= (Finset.range (n + 1)).sum (fun _k => Nat.choose n m) := by
        refine Finset.sum_le_sum ?_
        intro k _hk
        simpa [m] using Nat.choose_le_middle k n
      _ = (n + 1) * Nat.choose n m := by
        simp
  have hchoose_lower :
      (2 : Real) ^ n / ((n + 1 : Nat) : Real) <= (Nat.choose n m : Real) := by
    rw [div_le_iff₀ hB_pos]
    exact_mod_cast (by simpa [Nat.mul_comm] using hchoose_lower_nat)
  have hbase_le : ((2 : Real) ^ n / ((n + 1 : Nat) : Real)) * M <= S := by
    exact (mul_le_mul_of_nonneg_right hchoose_lower hM_pos.le).trans hsum_ge
  have hbase_pos : 0 < ((2 : Real) ^ n / ((n + 1 : Nat) : Real)) * M := by
    positivity
  have hS_pos : 0 < S := lt_of_lt_of_le hbase_pos hbase_le
  have hpow_two : (2 : Real) ^ n = 2 * (2 : Real) ^ (n - 1) := by
    calc
      (2 : Real) ^ n = (2 : Real) ^ ((n - 1) + 1) := by
        rw [Nat.sub_add_cancel hn_pos]
      _ = (2 : Real) ^ (n - 1) * 2 := by
        rw [pow_succ]
      _ = 2 * (2 : Real) ^ (n - 1) := by ring
  have hclosed :
      (2 : Real) ^ (n - 1) /
          (((2 : Real) ^ n / ((n + 1 : Nat) : Real)) * M) =
        ((n + 1 : Nat) : Real) / (2 * M) := by
    rw [hpow_two]
    field_simp [hB_pos.ne', hM_pos.ne']
  calc
    ((2 : Real) ^ (n - 1)) /
        ((Finset.Icc 1 n).sum
          (fun k => (Nat.choose n k : Real) * (k : Real) ^ (n - k)))
        = (2 : Real) ^ (n - 1) / S := by rfl
    _ <= (2 : Real) ^ (n - 1) /
        (((2 : Real) ^ n / ((n + 1 : Nat) : Real)) * M) := by
      exact div_le_div_of_nonneg_left (by positivity) hbase_pos hbase_le
    _ = ((n + 1 : Nat) : Real) / (2 * M) := hclosed
    _ = ((n + 1 : Nat) : Real) /
        (2 * ((n / 2 : Nat) : Real) ^ (n - n / 2)) := by rfl

end

end Omega.Zeta
