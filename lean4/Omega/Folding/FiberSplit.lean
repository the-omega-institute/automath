import Omega.Folding.MaxFiberHigh
import Omega.Folding.FiberArithmetic

namespace Omega

namespace X

noncomputable section

/-! ### D_m strict monotonicity

The maximum fiber multiplicity D(m) is strictly increasing for m ≥ 1.
Verified computationally for m ≤ 9, and conditionally for all m assuming
the two-step recurrence D(m) = D(m-2) + D(m-4) for m ≥ 6. -/

theorem maxFiber_lt_1_2 : maxFiberMultiplicity 1 < maxFiberMultiplicity 2 := by
  rw [maxFiberMultiplicity_one, maxFiberMultiplicity_two]; omega
theorem maxFiber_le_2_3 : maxFiberMultiplicity 2 ≤ maxFiberMultiplicity 3 := by
  rw [maxFiberMultiplicity_two, maxFiberMultiplicity_three]
theorem maxFiber_lt_3_4 : maxFiberMultiplicity 3 < maxFiberMultiplicity 4 := by
  rw [maxFiberMultiplicity_three, maxFiberMultiplicity_four]; omega
theorem maxFiber_lt_4_5 : maxFiberMultiplicity 4 < maxFiberMultiplicity 5 := by
  rw [maxFiberMultiplicity_four, maxFiberMultiplicity_five]; omega
theorem maxFiber_lt_5_6 : maxFiberMultiplicity 5 < maxFiberMultiplicity 6 := by
  rw [maxFiberMultiplicity_five, maxFiberMultiplicity_six]; omega
theorem maxFiber_lt_6_7 : maxFiberMultiplicity 6 < maxFiberMultiplicity 7 := by
  rw [maxFiberMultiplicity_six, maxFiberMultiplicity_seven]; omega
theorem maxFiber_lt_7_8 : maxFiberMultiplicity 7 < maxFiberMultiplicity 8 := by
  rw [maxFiberMultiplicity_seven, maxFiberMultiplicity_eight]; omega
theorem maxFiber_lt_8_9 : maxFiberMultiplicity 8 < maxFiberMultiplicity 9 := by
  rw [maxFiberMultiplicity_eight, maxFiberMultiplicity_nine]; omega
theorem maxFiber_lt_9_10 : maxFiberMultiplicity 9 < maxFiberMultiplicity 10 := by
  rw [maxFiberMultiplicity_nine, maxFiberMultiplicity_ten]; omega

/-- D(m) < D(m+1) for 3 ≤ m ≤ 9 (strict monotonicity, verified range).
    Note: D(2) = D(3) = 2, so strict monotonicity begins at m = 3.
    cor:pom-max-fiber-achievers-bsplit-strict-mono-verified -/
theorem maxFiberMultiplicity_strict_mono_verified (m : Nat) (hm1 : 3 ≤ m) (hm : m ≤ 9) :
    maxFiberMultiplicity m < maxFiberMultiplicity (m + 1) := by
  interval_cases m <;> first
    | exact maxFiber_lt_3_4 | exact maxFiber_lt_4_5 | exact maxFiber_lt_5_6
    | exact maxFiber_lt_6_7 | exact maxFiber_lt_7_8 | exact maxFiber_lt_8_9
    | exact maxFiber_lt_9_10

/-- D(m) ≤ D(m+1) for 1 ≤ m ≤ 9 (monotonicity, verified range).
    cor:pom-max-fiber-achievers-bsplit-mono-verified -/
theorem maxFiberMultiplicity_mono_verified (m : Nat) (hm1 : 1 ≤ m) (hm : m ≤ 9) :
    maxFiberMultiplicity m ≤ maxFiberMultiplicity (m + 1) := by
  interval_cases m <;> first
    | exact Nat.le_of_lt maxFiber_lt_1_2 | exact maxFiber_le_2_3
    | exact Nat.le_of_lt maxFiber_lt_3_4 | exact Nat.le_of_lt maxFiber_lt_4_5
    | exact Nat.le_of_lt maxFiber_lt_5_6 | exact Nat.le_of_lt maxFiber_lt_6_7
    | exact Nat.le_of_lt maxFiber_lt_7_8 | exact Nat.le_of_lt maxFiber_lt_8_9
    | exact Nat.le_of_lt maxFiber_lt_9_10

/-- D(m) is non-decreasing and eventually strictly increasing (m = 1..10). -/
theorem maxFiberMultiplicity_mono_conjunction :
    maxFiberMultiplicity 1 < maxFiberMultiplicity 2 ∧
    maxFiberMultiplicity 2 ≤ maxFiberMultiplicity 3 ∧
    maxFiberMultiplicity 3 < maxFiberMultiplicity 4 ∧
    maxFiberMultiplicity 4 < maxFiberMultiplicity 5 ∧
    maxFiberMultiplicity 5 < maxFiberMultiplicity 6 ∧
    maxFiberMultiplicity 6 < maxFiberMultiplicity 7 ∧
    maxFiberMultiplicity 7 < maxFiberMultiplicity 8 ∧
    maxFiberMultiplicity 8 < maxFiberMultiplicity 9 ∧
    maxFiberMultiplicity 9 < maxFiberMultiplicity 10 := by
  exact ⟨maxFiber_lt_1_2, maxFiber_le_2_3, maxFiber_lt_3_4, maxFiber_lt_4_5,
    maxFiber_lt_5_6, maxFiber_lt_6_7, maxFiber_lt_7_8, maxFiber_lt_8_9, maxFiber_lt_9_10⟩

/-- D(m) ≤ D(m+1) for all m ≥ 2, conditional on the two-step recurrence.
    cor:pom-max-fiber-achievers-bsplit-mono-of-two-step -/
theorem maxFiberMultiplicity_mono_of_two_step
    (two_step : ∀ m, 6 ≤ m → maxFiberMultiplicity m =
      maxFiberMultiplicity (m - 2) + maxFiberMultiplicity (m - 4))
    (m : Nat) (hm : 2 ≤ m) : maxFiberMultiplicity m ≤ maxFiberMultiplicity (m + 1) := by
  have hEven := maxFiberMultiplicity_even_of_two_step two_step
  have hOdd := maxFiberMultiplicity_odd_of_two_step two_step
  rcases Nat.even_or_odd' m with ⟨k, hk_eq | hk_eq⟩ <;> subst hk_eq
  · -- m = 2k: D(2k) = F(k+2), D(2k+1) = 2F(k+1)
    have hk : 1 ≤ k := by omega
    rw [hEven k hk, hOdd k hk]
    have hR := fib_succ_succ' k
    have hMono : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
    omega
  · -- m = 2k+1: D(2k+1) = 2F(k+1), D(2k+2) = F(k+3)
    have hk : 1 ≤ k := by omega
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by ring]
    rw [hOdd k hk, hEven (k + 1) (by omega)]
    -- Goal: 2 * Nat.fib (k + 1) ≤ Nat.fib (k + 1 + 2)
    have hR : Nat.fib (k + 1 + 2) = Nat.fib (k + 1 + 1) + Nat.fib (k + 1) :=
      fib_succ_succ' (k + 1)
    have hMono : Nat.fib (k + 1) ≤ Nat.fib (k + 1 + 1) := Nat.fib_mono (by omega)
    omega

/-- D(m) < D(m+1) for all m ≥ 3, conditional on the two-step recurrence.
    Note: D(2) = D(3), so strict monotonicity requires m ≥ 3.
    cor:pom-max-fiber-achievers-bsplit-strict-mono-of-two-step -/
theorem maxFiberMultiplicity_strict_mono_of_two_step
    (two_step : ∀ m, 6 ≤ m → maxFiberMultiplicity m =
      maxFiberMultiplicity (m - 2) + maxFiberMultiplicity (m - 4))
    (m : Nat) (hm : 3 ≤ m) : maxFiberMultiplicity m < maxFiberMultiplicity (m + 1) := by
  have hEven := maxFiberMultiplicity_even_of_two_step two_step
  have hOdd := maxFiberMultiplicity_odd_of_two_step two_step
  rcases Nat.even_or_odd' m with ⟨k, hk_eq | hk_eq⟩ <;> subst hk_eq
  · -- m = 2k (≥ 4 since m ≥ 3 and even): D(2k) = F(k+2) < 2F(k+1) = D(2k+1)
    have hk : 2 ≤ k := by omega
    rw [hEven k (by omega), hOdd k (by omega)]
    -- Goal: Nat.fib (k + 2) < 2 * Nat.fib (k + 1)
    have hR : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := fib_succ_succ' k
    have hStrict : Nat.fib k < Nat.fib (k + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      exact fib_lt_fib_succ j
    omega
  · -- m = 2k+1 (≥ 3): D(2k+1) = 2F(k+1) < F(k+3) = D(2k+2)
    have hk : 1 ≤ k := by omega
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by ring]
    rw [hOdd k hk, hEven (k + 1) (by omega)]
    -- Goal: 2 * Nat.fib (k + 1) < Nat.fib (k + 1 + 2)
    have hR : Nat.fib (k + 1 + 2) = Nat.fib (k + 1 + 1) + Nat.fib (k + 1) :=
      fib_succ_succ' (k + 1)
    have hStrict : Nat.fib (k + 1) < Nat.fib (k + 1 + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact fib_lt_fib_succ j
    omega

/-- D determines m: if D(m) = D(n) and both m, n ≤ 10, then m = n.
    The D values for m = 0..10 are: 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 13.
    Injectivity holds for m, n ≥ 3 (or {0,1} and {2,3} separately). -/
theorem maxFiberMultiplicity_injective_verified (m n : Nat) (hm : m ≤ 10) (hn : n ≤ 10)
    (h : maxFiberMultiplicity m = maxFiberMultiplicity n) : m = n ∨
    (m ≤ 1 ∧ n ≤ 1) ∨ (2 ≤ m ∧ m ≤ 3 ∧ 2 ≤ n ∧ n ≤ 3) := by
  interval_cases m <;> interval_cases n <;> simp_all [
    maxFiberMultiplicity_zero, maxFiberMultiplicity_one, maxFiberMultiplicity_two,
    maxFiberMultiplicity_three, maxFiberMultiplicity_four, maxFiberMultiplicity_five,
    maxFiberMultiplicity_six, maxFiberMultiplicity_seven, maxFiberMultiplicity_eight,
    maxFiberMultiplicity_nine, maxFiberMultiplicity_ten]

/-- D is injective on {3, 4, ..., 10}: if D(m) = D(n) and 3 ≤ m, n ≤ 10, then m = n. -/
theorem maxFiberMultiplicity_injective_from_three (m n : Nat)
    (hm1 : 3 ≤ m) (hm : m ≤ 10) (hn1 : 3 ≤ n) (hn : n ≤ 10)
    (h : maxFiberMultiplicity m = maxFiberMultiplicity n) : m = n := by
  interval_cases m <;> interval_cases n <;> simp_all [
    maxFiberMultiplicity_three, maxFiberMultiplicity_four, maxFiberMultiplicity_five,
    maxFiberMultiplicity_six, maxFiberMultiplicity_seven, maxFiberMultiplicity_eight,
    maxFiberMultiplicity_nine, maxFiberMultiplicity_ten]

/-! ### Fiber splitting bounds

D(m+2) ≤ D(m+1) + D(m) is proved as `maxFiberMultiplicity_le_add`. -/

/-- The fiber splitting inequality: D(m+2) ≤ D(m+1) + D(m) (named wrapper).
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem maxFiberMultiplicity_split_bound (m : Nat) :
    maxFiberMultiplicity (m + 2) ≤ maxFiberMultiplicity (m + 1) + maxFiberMultiplicity m :=
  maxFiberMultiplicity_le_add m

/-- The fiber splitting in descending index form: D(m) ≤ D(m-1) + D(m-2) for m ≥ 4.
    cor:pom-max-fiber-fibonacci-bound -/
theorem maxFiberMultiplicity_fibonacci_bound (m : Nat) (hm : 4 ≤ m) :
    maxFiberMultiplicity m ≤ maxFiberMultiplicity (m - 1) + maxFiberMultiplicity (m - 2) := by
  have h := maxFiberMultiplicity_le_add (m - 2)
  rw [show m - 2 + 2 = m from by omega, show m - 2 + 1 = m - 1 from by omega] at h
  exact h

/-! ### Second-largest fiber multiplicity

The computable second-largest fiber multiplicity D^{(2)}(m) is the max of d(x) over
all x ∈ X_m with d(x) < D(m). Computed values:
D^{(2)}(2)=1, D^{(2)}(3)=1, D^{(2)}(4)=2, D^{(2)}(5)=3, D^{(2)}(6)=4, D^{(2)}(7)=5.

For m ≥ 4: D^{(2)}(m) = D(m-1). -/

/-- Computable second-largest fiber multiplicity.
    def:pom-top-fiber-spectrum-second -/
def cSecondMaxFiberMult (m : Nat) : Nat :=
  let S := (@Finset.univ (X m) (fintypeX m))
  let maxVal := cMaxFiberMult m
  let below := S.filter (fun x => cFiberMult x < maxVal)
  if h : below.Nonempty then below.sup' h (fun x => cFiberMult x) else 0

/-- D^{(2)} base values.
    cor:pom-second-max-fiber-base-2 -/
theorem cSecondMaxFiberMult_two : cSecondMaxFiberMult 2 = 1 := by native_decide
/-- cor:pom-second-max-fiber-base-3 -/
theorem cSecondMaxFiberMult_three : cSecondMaxFiberMult 3 = 1 := by native_decide
/-- cor:pom-second-max-fiber-base-4 -/
theorem cSecondMaxFiberMult_four : cSecondMaxFiberMult 4 = 2 := by native_decide
/-- cor:pom-second-max-fiber-base-5 -/
theorem cSecondMaxFiberMult_five : cSecondMaxFiberMult 5 = 3 := by native_decide
/-- cor:pom-second-max-fiber-base-6 -/
theorem cSecondMaxFiberMult_six : cSecondMaxFiberMult 6 = 4 := by native_decide
/-- cor:pom-second-max-fiber-base-7 -/
theorem cSecondMaxFiberMult_seven : cSecondMaxFiberMult 7 = 5 := by native_decide

/-- D^{(2)}(m) = D(m-1) for m = 4..7.
    cor:pom-second-max-fiber-eq-prev -/
theorem cSecondMaxFiberMult_eq_prev (m : Nat) (hm1 : 4 ≤ m) (hm : m ≤ 7) :
    cSecondMaxFiberMult m = cMaxFiberMult (m - 1) := by
  interval_cases m <;> native_decide

/-! ### Fiber splitting structural lemma (false-ending case)

When the last bit is false, truncation preserves the fiber-restrict relationship. -/

/-- Reconstruction: w = snoc (truncate w) (w[m]). -/
private theorem snoc_truncate_last' {m : Nat} (w : Word (m + 1)) :
    snoc (truncate w) (w ⟨m, Nat.lt_succ_self m⟩) = w := by
  funext i; by_cases h : i.1 < m
  · simp [snoc, truncate, h]
  · have : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt h)
    subst this; simp [snoc]

/-- Truncating a false-ending word preserves the fiber-restrict relationship. -/
theorem truncate_Fold_eq_restrict_of_false {m : Nat} (w : Word (m + 1))
    (hLast : w ⟨m, Nat.lt_succ_self m⟩ = false) :
    Fold (truncate w) = X.restrict (Fold w) := by
  -- Fold w = Fold (snoc (truncate w) false)
  have hRecon : Fold w = Fold (snoc (truncate w) false) := by
    congr 1; rw [← hLast]; exact (snoc_truncate_last' w).symm
  rw [hRecon]
  -- X.restrict (Fold (snoc (truncate w) false)) = Fold (truncate w)
  -- by restrict_Fold_snoc_false
  show Fold (truncate w) = X.restrict (Fold (snoc (truncate w) false))
  -- restrict_Fold_snoc_false : X.restrict (Fold (snoc v false)) = Fold v
  -- for v : Word (n + 1). Here v = truncate w : Word m.
  -- Need m = n + 1, i.e., m ≥ 1. Handle m = 0 separately.
  cases m with
  | zero =>
    -- truncate w : Word 0, Fold (truncate w) : X 0
    -- snoc (truncate w) false : Word 1
    -- Both sides should agree trivially for the single element of X 0.
    apply Subtype.ext; funext ⟨i, hi⟩; exact absurd hi (Nat.not_lt_zero _)
  | succ n =>
    exact (restrict_Fold_snoc_false (truncate w)).symm

/-- If Fold w = x and the last bit is false, then Fold(truncate w) = restrict(x). -/
theorem truncate_mem_fiber_restrict_false {m : Nat} (x : X (m + 1)) (w : Word (m + 1))
    (hw : Fold w = x) (h : w ⟨m, Nat.lt_succ_self m⟩ = false) :
    Fold (truncate w) = X.restrict x := by
  rw [← hw]; exact truncate_Fold_eq_restrict_of_false w h

/-! ### Max fiber strictly less than word count -/

/-- D(m) < 2^m for 2 ≤ m ≤ 10: the max fiber is strictly smaller than total word count.
    cor:pom-max-fiber-rate-endpoint -/
theorem maxFiber_lt_half_wordcount (m : Nat) (hm : 2 ≤ m) (hm' : m ≤ 10) :
    maxFiberMultiplicity m < 2 ^ m := by
  interval_cases m <;> simp only [
    maxFiberMultiplicity_two, maxFiberMultiplicity_three, maxFiberMultiplicity_four,
    maxFiberMultiplicity_five, maxFiberMultiplicity_six, maxFiberMultiplicity_seven,
    maxFiberMultiplicity_eight, maxFiberMultiplicity_nine, maxFiberMultiplicity_ten] <;> omega

-- ══════════════════════════════════════════════════════════════
-- Phase 213: Fibonacci gap recurrence + alternative second-max identity
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci gap recurrence: F(k+2)-F(k-4) = (F(k+1)-F(k-5)) + (F(k)-F(k-6)) for k≥6.
    lem:pom-forbidden-pair-fib-gap -/
theorem fib_gap_recurrence (k : Nat) (hk : 6 ≤ k) :
    Nat.fib (k + 2) - Nat.fib (k - 4) =
    (Nat.fib (k + 1) - Nat.fib (k - 5)) + (Nat.fib k - Nat.fib (k - 6)) := by
  have hrec1 := Nat.fib_add_two (n := k)
  have hrec2 := Nat.fib_add_two (n := k - 6)
  have hk4 : k - 4 = (k - 6) + 2 := by omega
  have hk5 : k - 5 = (k - 6) + 1 := by omega
  rw [hk4, hk5]
  rw [Nat.fib_add_two (n := k - 6)] at *
  -- Now all subtractions are safe due to Fibonacci monotonicity
  have hle1 : Nat.fib (k - 6) + Nat.fib (k - 6 + 1) ≤ Nat.fib (k + 1) :=
    Nat.fib_add_two ▸ Nat.fib_mono (by omega)
  have hle2 : Nat.fib (k - 6 + 1) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have hle3 : Nat.fib (k - 6) ≤ Nat.fib k := Nat.fib_mono (by omega)
  omega

-- Note: cSecondMaxFiberMult_even_closed deferred — requires recursive infrastructure
-- for cSecondMaxFiberMult beyond base cases. The fib_gap_recurrence above provides
-- the key Fibonacci identity needed for the eventual proof.

end
end X

-- ══════════════════════════════════════════════════════════════
-- Phase 231: D(m) = D(m-2) + D(m-4) four-step recurrence
-- ══════════════════════════════════════════════════════════════

/-- D(m) = D(m-2) + D(m-4) for 6 ≤ m ≤ 10 (verified range). cor:pom-D-rec -/
theorem maxFiberMultiplicity_four_step_verified (m : Nat) (hm1 : 6 ≤ m) (hm2 : m ≤ 10) :
    X.maxFiberMultiplicity m =
    X.maxFiberMultiplicity (m - 2) + X.maxFiberMultiplicity (m - 4) := by
  interval_cases m
  · exact X.maxFiberMultiplicity_two_step_6
  · exact X.maxFiberMultiplicity_two_step_7
  · exact X.maxFiberMultiplicity_two_step_8
  · exact X.maxFiberMultiplicity_two_step_9
  · exact X.maxFiberMultiplicity_two_step_10

/-- Four-step upper bound: D(m+4) ≤ 2·D(m+2) + D(m+1) + D(m).
    Follows from two applications of the splitting inequality D(n+2) ≤ D(n+1) + D(n).
    cor:pom-D-rec-four-step -/
theorem maxFiberMultiplicity_four_step (m : Nat) (_hm : 2 ≤ m) :
    X.maxFiberMultiplicity (m + 4) ≤
    2 * X.maxFiberMultiplicity (m + 2) + X.maxFiberMultiplicity (m + 1) +
    X.maxFiberMultiplicity m := by
  have h1 := X.maxFiberMultiplicity_le_add (m + 2)
  have h2 := X.maxFiberMultiplicity_le_add (m + 1)
  -- h1: D(m+4) ≤ D(m+3) + D(m+2)
  -- h2: D(m+3) ≤ D(m+2) + D(m+1)
  -- Combined: D(m+4) ≤ 2·D(m+2) + D(m+1) ≤ 2·D(m+2) + D(m+1) + D(m)
  have hpos : 0 ≤ X.maxFiberMultiplicity m := Nat.zero_le _
  linarith

end Omega
