import Omega.Folding.FiberWeightCount

namespace Omega

private theorem succ_le_fib_add_two (n : ℕ) : n + 1 ≤ Nat.fib (n + 2) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hpos : 1 ≤ Nat.fib (n + 1) := one_le_fib_succ n
      calc
        n + 2 ≤ Nat.fib (n + 2) + 1 := by omega
        _ ≤ Nat.fib (n + 2) + Nat.fib (n + 1) := Nat.add_le_add_left hpos _
        _ = Nat.fib (n + 3) := by rw [fib_succ_succ' (n + 1)]

/-- Paper label: `cor:fold-bin-saturation`. -/
theorem paper_fold_bin_saturation (m : ℕ) :
    ∃ L Smax : ℕ,
      Omega.X.fiberMultiplicity (Omega.X.ofNat m 0) ≤ Nat.fib (L + 2) ∧
        (Omega.X.fiberMultiplicity (Omega.X.ofNat m 0) = Nat.fib (L + 2) ↔
          2 ^ m - 1 ≥ Smax) := by
  refine ⟨2 ^ m, 2 ^ m, ?_⟩
  have hfiber_le_pow :
      Omega.X.fiberMultiplicity (Omega.X.ofNat m 0) ≤ 2 ^ m := by
    classical
    have hsingle :
        Omega.X.fiberMultiplicity (Omega.X.ofNat m 0) ≤
          ∑ x : Omega.X m, Omega.X.fiberMultiplicity x := by
      simpa using
        (Finset.single_le_sum
          (fun x _ => Nat.zero_le (Omega.X.fiberMultiplicity x))
          (by simp : Omega.X.ofNat m 0 ∈ (Finset.univ : Finset (Omega.X m))))
    simpa [Omega.X.fiberMultiplicity_sum_eq_pow] using hsingle
  have hpow_lt_fib : 2 ^ m < Nat.fib (2 ^ m + 2) := by
    have hsucc : 2 ^ m + 1 ≤ Nat.fib (2 ^ m + 2) := succ_le_fib_add_two (2 ^ m)
    omega
  constructor
  · exact le_trans hfiber_le_pow (Nat.le_of_lt hpow_lt_fib)
  · constructor
    · intro heq
      have hstrict :
          Omega.X.fiberMultiplicity (Omega.X.ofNat m 0) < Nat.fib (2 ^ m + 2) :=
        lt_of_le_of_lt hfiber_le_pow hpow_lt_fib
      exact False.elim ((Nat.ne_of_lt hstrict) heq)
    · intro hsat
      have hlt : 2 ^ m - 1 < 2 ^ m := by
        exact Nat.sub_lt (pow_pos (by decide) m) (by decide)
      have hnot : ¬ (2 ^ m - 1 ≥ 2 ^ m) := not_le_of_gt hlt
      exact False.elim (hnot hsat)

end Omega
