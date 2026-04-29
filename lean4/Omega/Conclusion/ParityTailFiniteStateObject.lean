import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_parity_tail_finite_state_object_reduce_add_mul (S : ℕ → Bool) (N P : ℕ)
    (hper : ∀ m, N ≤ m → S (m + P) = S m) (q r : ℕ) :
    S (N + (r + q * P)) = S (N + r) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have htail : N ≤ N + (r + q * P) := Nat.le_add_right _ _
      calc
        S (N + (r + Nat.succ q * P)) = S ((N + (r + q * P)) + P) := by
          congr 1
          rw [Nat.succ_mul]
          omega
        _ = S (N + (r + q * P)) := hper _ htail
        _ = S (N + r) := ih

lemma conclusion_parity_tail_finite_state_object_reduce_mod (S : ℕ → Bool) (N P : ℕ)
    (hper : ∀ m, N ≤ m → S (m + P) = S m) (k : ℕ) :
    S (N + k) = S (N + k % P) := by
  have hk : k = k % P + k / P * P := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div k P).symm
  calc
    S (N + k) = S (N + (k % P + k / P * P)) := congrArg (fun x => S (N + x)) hk
    _ = S (N + k % P) :=
      conclusion_parity_tail_finite_state_object_reduce_add_mul S N P hper (k / P) (k % P)

/-- Paper label: `cor:conclusion-parity-tail-finite-state-object`. -/
theorem paper_conclusion_parity_tail_finite_state_object (S : ℕ → Bool) (N P : ℕ)
    (hP0 : 0 < P) (hP16 : P ≤ 16)
    (hper : ∀ m, N ≤ m → S (m + P) = S m) :
    ∃ σ : Fin P → Bool, ∀ m, N ≤ m →
      S m = σ ⟨(m - N) % P, Nat.mod_lt (m - N) hP0⟩ := by
  have _ : P ≤ 16 := hP16
  refine ⟨fun r => S (N + r.1), ?_⟩
  intro m hm
  calc
    S m = S (N + (m - N)) := congrArg S (Nat.add_sub_of_le hm).symm
    _ = S (N + (m - N) % P) :=
      conclusion_parity_tail_finite_state_object_reduce_mod S N P hper (m - N)
    _ = (fun r : Fin P => S (N + r.1))
        ⟨(m - N) % P, Nat.mod_lt (m - N) hP0⟩ := rfl

end Omega.Conclusion
