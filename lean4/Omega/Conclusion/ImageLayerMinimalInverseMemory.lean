import Mathlib.Tactic

namespace Omega.Conclusion

/-- Synchronisation depth at window size `m`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
def dSync (m : ℕ) : ℕ := m - 1

/-- Closed form.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_eq (m : ℕ) : dSync m = m - 1 := rfl

/-- Strict monotonicity of `dSync` from `m ≥ 3`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_strict_mono {m n : ℕ} (hm : 3 ≤ m) (hmn : m < n) :
    dSync m < dSync n := by
  unfold dSync; omega

/-- Minimal memory is exactly `m - 1` once it is sandwiched between `m - 1` and
    `m - 1`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem minMemory_eq_of_bounded (m memMin : ℕ) (_hm : 3 ≤ m)
    (hUpper : memMin ≤ m - 1) (hLower : m - 1 ≤ memMin) :
    memMin = m - 1 := by
  omega

/-- Same as above, expressed in terms of `dSync m`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem minMemory_eq_dSync (m memMin : ℕ) (_hm : 3 ≤ m)
    (hUpper : memMin ≤ dSync m) (hLower : dSync m ≤ memMin) :
    memMin = dSync m :=
  le_antisymm hUpper hLower

/-- Lower-bound contradiction: if the memory budget is at most `m - 2`, the
    required synchronisation depth `dSync m = m - 1` strictly exceeds it.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_exceeds_insufficient_memory (m memMin : ℕ)
    (hm : 3 ≤ m) (hSmall : memMin ≤ m - 2) :
    dSync m > memMin := by
  unfold dSync; omega

/-- Paper package: image-layer minimal inverse memory scaffolding.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem paper_image_layer_minimal_inverse_memory :
    (∀ m : ℕ, dSync m = m - 1) ∧
    (∀ m n : ℕ, 3 ≤ m → m < n → dSync m < dSync n) ∧
    (∀ (m memMin : ℕ), 3 ≤ m → memMin ≤ m - 1 → m - 1 ≤ memMin → memMin = m - 1) ∧
    (∀ (m memMin : ℕ), 3 ≤ m → memMin ≤ m - 2 → dSync m > memMin) ∧
    (∀ (m memMin : ℕ), 3 ≤ m → memMin ≤ dSync m → dSync m ≤ memMin → memMin = dSync m) :=
  ⟨dSync_eq,
   fun _ _ => dSync_strict_mono,
   minMemory_eq_of_bounded,
   dSync_exceeds_insufficient_memory,
   minMemory_eq_dSync⟩

/-- dSync grows linearly while 2^dSync grows exponentially.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_exponential_gap (m : ℕ) (_hm : 3 ≤ m) :
    dSync m < 2 ^ dSync m := by
  unfold dSync
  exact Nat.lt_pow_self (by decide : 1 < 2)

/-- Fibonacci comparison: F_{m+2} vs 2^{m-1} for small m.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem fib_vs_pow_dSync_seeds :
    (2 ^ dSync 3 < Nat.fib 5) ∧
    (2 ^ dSync 4 ≤ Nat.fib 6) ∧
    (Nat.fib 7 < 2 ^ dSync 5) ∧
    (Nat.fib 8 < 2 ^ dSync 6) ∧
    (Nat.fib 12 < 2 ^ dSync 10) := by
  decide

/-- The crossover point: smallest m where 2^{m-1} > F_{m+2}.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem crossover_point :
    (2 ^ 3 = Nat.fib 6) ∧
    (Nat.fib 7 < 2 ^ 4) ∧
    (2 ^ 2 < Nat.fib 5) := by
  decide

/-- Paper package: sync depth + Fibonacci crossover.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem paper_sync_depth_fibonacci_crossover :
    (dSync 3 = 2 ∧ dSync 4 = 3 ∧ dSync 5 = 4 ∧ dSync 6 = 5) ∧
    (2 ^ 2 < Nat.fib 5) ∧
    (2 ^ 3 = Nat.fib 6) ∧
    (Nat.fib 7 < 2 ^ 4) ∧
    (Nat.fib 8 < 2 ^ 5) ∧
    (Nat.fib 10 < 2 ^ 7) := by
  decide

end Omega.Conclusion
