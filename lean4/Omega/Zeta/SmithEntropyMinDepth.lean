import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Smith entropy of a multiset of exponents at depth `k`: sum of pointwise
    mins with `k`.
    cor:xi-smith-entropy-minimal-depth -/
def smithEntropy (s : Multiset ℕ) (k : ℕ) : ℕ :=
  (s.map (fun v => min v k)).sum

/-- Smith increment: number of entries ≥ `k`.
    cor:xi-smith-entropy-minimal-depth -/
def smithDelta (s : Multiset ℕ) (k : ℕ) : ℕ :=
  (s.filter (fun v => k ≤ v)).card

/-- `smithEntropy s 0 = 0`.
    cor:xi-smith-entropy-minimal-depth -/
theorem smithEntropy_zero (s : Multiset ℕ) : smithEntropy s 0 = 0 := by
  unfold smithEntropy
  induction s using Multiset.induction with
  | empty => simp
  | cons v t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    simp

/-- `smithDelta s 0 = s.card` (every entry is ≥ 0).
    cor:xi-smith-entropy-minimal-depth -/
theorem smithDelta_zero (s : Multiset ℕ) : smithDelta s 0 = s.card := by
  unfold smithDelta
  congr 1
  exact Multiset.filter_eq_self.mpr (fun _ _ => Nat.zero_le _)

/-- Smith entropy is monotone in depth.
    cor:xi-smith-entropy-minimal-depth -/
theorem smithEntropy_mono_succ (s : Multiset ℕ) (k : ℕ) :
    smithEntropy s k ≤ smithEntropy s (k + 1) := by
  unfold smithEntropy
  induction s using Multiset.induction with
  | empty => simp
  | cons v t ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have hmin : min v k ≤ min v (k + 1) :=
      min_le_min_left v (Nat.le_succ k)
    exact Nat.add_le_add hmin ih

/-- If every entry is already ≤ `k`, Smith entropy equals the total sum.
    cor:xi-smith-entropy-minimal-depth -/
theorem smithEntropy_eq_sum_of_all_le (s : Multiset ℕ) (k : ℕ)
    (h : ∀ v ∈ s, v ≤ k) :
    smithEntropy s k = s.sum := by
  unfold smithEntropy
  induction s using Multiset.induction with
  | empty => simp
  | cons v t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have hv : v ≤ k := h v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≤ k := fun w hw => h w (Multiset.mem_cons_of_mem hw)
    rw [Nat.min_eq_left hv, ih ht]

/-- Main recursion: entropy increment at step `k+1` counts exactly the
    multiplicity of entries ≥ `k+1`.
    cor:xi-smith-entropy-minimal-depth -/
theorem smithEntropy_succ_eq_add_delta (s : Multiset ℕ) (k : ℕ) :
    smithEntropy s (k + 1) = smithEntropy s k + smithDelta s (k + 1) := by
  unfold smithEntropy smithDelta
  induction s using Multiset.induction with
  | empty => simp
  | cons v t ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    by_cases hv : k + 1 ≤ v
    · rw [Multiset.filter_cons_of_pos _ hv, Multiset.card_cons]
      have h1 : min v (k + 1) = k + 1 := by omega
      have h2 : min v k = k := by omega
      rw [h1, h2, ih]
      ring
    · rw [Multiset.filter_cons_of_neg _ hv]
      have hv' : v ≤ k := by omega
      have h1 : min v (k + 1) = v := by omega
      have h2 : min v k = v := by omega
      rw [h1, h2, ih]
      ring

/-- Paper package: Smith entropy discrete semicontinuity scaffolding.
    cor:xi-smith-entropy-minimal-depth -/
theorem paper_xi_smith_entropy_minimal_depth :
    (∀ s : Multiset ℕ, smithEntropy s 0 = 0) ∧
    (∀ s : Multiset ℕ, smithDelta s 0 = s.card) ∧
    (∀ (s : Multiset ℕ) (k : ℕ), smithEntropy s k ≤ smithEntropy s (k + 1)) ∧
    (∀ (s : Multiset ℕ) (k : ℕ), (∀ v ∈ s, v ≤ k) → smithEntropy s k = s.sum) ∧
    (∀ (s : Multiset ℕ) (k : ℕ),
      smithEntropy s (k + 1) = smithEntropy s k + smithDelta s (k + 1)) :=
  ⟨smithEntropy_zero, smithDelta_zero, smithEntropy_mono_succ,
   smithEntropy_eq_sum_of_all_le, smithEntropy_succ_eq_add_delta⟩

end Omega.Zeta
