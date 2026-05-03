import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite data for the `k`-parallel 4-ary stopping-time law. -/
structure xi_coherence_stopping_time_k_parallel_4ary_data where
  xi_coherence_stopping_time_k_parallel_4ary_k : ℕ
  xi_coherence_stopping_time_k_parallel_4ary_N : ℕ
  xi_coherence_stopping_time_k_parallel_4ary_k_pos :
    0 < xi_coherence_stopping_time_k_parallel_4ary_k
  xi_coherence_stopping_time_k_parallel_4ary_N_pos :
    0 < xi_coherence_stopping_time_k_parallel_4ary_N

namespace xi_coherence_stopping_time_k_parallel_4ary_data

noncomputable def xi_coherence_stopping_time_k_parallel_4ary_same_component
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) : ℚ :=
  1 / (D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ)

noncomputable def xi_coherence_stopping_time_k_parallel_4ary_same_truncation
    (n : ℕ) : ℚ :=
  1 / (4 : ℚ) ^ n

noncomputable def xi_coherence_stopping_time_k_parallel_4ary_tail
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) (n : ℕ) : ℚ :=
  if n = 0 then 1
  else
    xi_coherence_stopping_time_k_parallel_4ary_same_component D *
      xi_coherence_stopping_time_k_parallel_4ary_same_truncation n

noncomputable def xi_coherence_stopping_time_k_parallel_4ary_point
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) (n : ℕ) : ℚ :=
  if n = 0 then 0
  else if n = 1 then
    1 - xi_coherence_stopping_time_k_parallel_4ary_tail D 1
  else if n ≤ D.xi_coherence_stopping_time_k_parallel_4ary_N then
    xi_coherence_stopping_time_k_parallel_4ary_tail D (n - 1) -
      xi_coherence_stopping_time_k_parallel_4ary_tail D n
  else if n = D.xi_coherence_stopping_time_k_parallel_4ary_N + 1 then
    xi_coherence_stopping_time_k_parallel_4ary_tail D
      D.xi_coherence_stopping_time_k_parallel_4ary_N
  else
    0

noncomputable def xi_coherence_stopping_time_k_parallel_4ary_expected
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) : ℚ :=
  1 +
    (1 / (D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ)) *
      Finset.sum (Finset.range D.xi_coherence_stopping_time_k_parallel_4ary_N)
        (fun n => (1 / (4 : ℚ) ^ (n + 1)))

lemma xi_coherence_stopping_time_k_parallel_4ary_finite_geometric_sum
    (N : ℕ) :
    Finset.sum (Finset.range N) (fun n => (1 / (4 : ℚ) ^ (n + 1))) =
      (1 / 3 : ℚ) * (1 - 1 / (4 : ℚ) ^ N) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf

lemma xi_coherence_stopping_time_k_parallel_4ary_tail_law
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) {n : ℕ}
    (hn : 1 ≤ n) :
    xi_coherence_stopping_time_k_parallel_4ary_tail D n =
      1 / ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) * (4 : ℚ) ^ n) := by
  have hn0 : n ≠ 0 := by omega
  simp [xi_coherence_stopping_time_k_parallel_4ary_tail,
    xi_coherence_stopping_time_k_parallel_4ary_same_component,
    xi_coherence_stopping_time_k_parallel_4ary_same_truncation, hn0]
  field_simp

lemma xi_coherence_stopping_time_k_parallel_4ary_point_first
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) :
    xi_coherence_stopping_time_k_parallel_4ary_point D 1 =
      1 - 1 / ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) * 4) := by
  rw [xi_coherence_stopping_time_k_parallel_4ary_point]
  simp
  rw [xi_coherence_stopping_time_k_parallel_4ary_tail_law D (by norm_num : 1 ≤ 1)]
  norm_num

lemma xi_coherence_stopping_time_k_parallel_4ary_point_middle
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) {n : ℕ}
    (h2 : 2 ≤ n) (hN : n ≤ D.xi_coherence_stopping_time_k_parallel_4ary_N) :
    xi_coherence_stopping_time_k_parallel_4ary_point D n =
      3 / ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) * (4 : ℚ) ^ n) := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  rw [xi_coherence_stopping_time_k_parallel_4ary_point]
  simp [hn0, hn1, hN]
  rw [xi_coherence_stopping_time_k_parallel_4ary_tail_law D (by omega : 1 ≤ n - 1),
    xi_coherence_stopping_time_k_parallel_4ary_tail_law D (by omega : 1 ≤ n)]
  have hn : (n - 1) + 1 = n := by omega
  have hpow : (4 : ℚ) ^ n = (4 : ℚ) ^ (n - 1) * 4 := by
    calc
      (4 : ℚ) ^ n = (4 : ℚ) ^ ((n - 1) + 1) := by rw [hn]
      _ = (4 : ℚ) ^ (n - 1) * 4 := by exact pow_succ (4 : ℚ) (n - 1)
  rw [hpow]
  field_simp
  ring

lemma xi_coherence_stopping_time_k_parallel_4ary_point_terminal
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) :
    xi_coherence_stopping_time_k_parallel_4ary_point D
        (D.xi_coherence_stopping_time_k_parallel_4ary_N + 1) =
      1 /
        ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) *
          (4 : ℚ) ^ D.xi_coherence_stopping_time_k_parallel_4ary_N) := by
  have hN0 : D.xi_coherence_stopping_time_k_parallel_4ary_N ≠ 0 :=
    Nat.ne_of_gt D.xi_coherence_stopping_time_k_parallel_4ary_N_pos
  have hnot0 : D.xi_coherence_stopping_time_k_parallel_4ary_N + 1 ≠ 0 := by omega
  have hnot1 : D.xi_coherence_stopping_time_k_parallel_4ary_N + 1 ≠ 1 := by
    omega
  have hle :
      ¬ D.xi_coherence_stopping_time_k_parallel_4ary_N + 1 ≤
        D.xi_coherence_stopping_time_k_parallel_4ary_N := by
    omega
  rw [xi_coherence_stopping_time_k_parallel_4ary_point]
  simp [hN0, hle]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    xi_coherence_stopping_time_k_parallel_4ary_tail_law D
      D.xi_coherence_stopping_time_k_parallel_4ary_N_pos

lemma xi_coherence_stopping_time_k_parallel_4ary_expected_closed
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) :
    xi_coherence_stopping_time_k_parallel_4ary_expected D =
      1 +
        (1 / (3 * (D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ))) *
          (1 - 1 / (4 : ℚ) ^ D.xi_coherence_stopping_time_k_parallel_4ary_N) := by
  rw [xi_coherence_stopping_time_k_parallel_4ary_expected,
    xi_coherence_stopping_time_k_parallel_4ary_finite_geometric_sum]
  ring

noncomputable def statement
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) : Prop :=
  (∀ n,
      1 ≤ n →
      n ≤ D.xi_coherence_stopping_time_k_parallel_4ary_N →
        xi_coherence_stopping_time_k_parallel_4ary_tail D n =
          1 / ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) * (4 : ℚ) ^ n)) ∧
    xi_coherence_stopping_time_k_parallel_4ary_point D 1 =
      1 - 1 / ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) * 4) ∧
    (∀ n,
      2 ≤ n →
      n ≤ D.xi_coherence_stopping_time_k_parallel_4ary_N →
        xi_coherence_stopping_time_k_parallel_4ary_point D n =
          3 / ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) * (4 : ℚ) ^ n)) ∧
    xi_coherence_stopping_time_k_parallel_4ary_point D
        (D.xi_coherence_stopping_time_k_parallel_4ary_N + 1) =
      1 /
        ((D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ) *
          (4 : ℚ) ^ D.xi_coherence_stopping_time_k_parallel_4ary_N) ∧
    xi_coherence_stopping_time_k_parallel_4ary_expected D =
      1 +
        (1 / (3 * (D.xi_coherence_stopping_time_k_parallel_4ary_k : ℚ))) *
          (1 - 1 / (4 : ℚ) ^ D.xi_coherence_stopping_time_k_parallel_4ary_N)

end xi_coherence_stopping_time_k_parallel_4ary_data

open xi_coherence_stopping_time_k_parallel_4ary_data

/-- Paper label: `thm:xi-coherence-stopping-time-k-parallel-4ary`. -/
theorem paper_xi_coherence_stopping_time_k_parallel_4ary
    (D : xi_coherence_stopping_time_k_parallel_4ary_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn _hN
    exact xi_coherence_stopping_time_k_parallel_4ary_tail_law D hn
  · exact xi_coherence_stopping_time_k_parallel_4ary_point_first D
  · intro n h2 hN
    exact xi_coherence_stopping_time_k_parallel_4ary_point_middle D h2 hN
  · exact xi_coherence_stopping_time_k_parallel_4ary_point_terminal D
  · exact xi_coherence_stopping_time_k_parallel_4ary_expected_closed D

end Omega.Zeta
