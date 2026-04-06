import Mathlib.Tactic
import Omega.Zeta.DynZeta

namespace Omega.Discussion

/-- Chebyshev-Adams polynomial: C_d(S) = 2·T_d(S/2).
    thm:discussion-chebyshev-witt-equivariance -/
def chebyAdams : ℕ → ℤ → ℤ
  | 0, _ => 2
  | 1, S => S
  | n + 2, S => S * chebyAdams (n + 1) S - chebyAdams n S

@[simp] theorem chebyAdams_zero (S : ℤ) : chebyAdams 0 S = 2 := rfl
@[simp] theorem chebyAdams_one (S : ℤ) : chebyAdams 1 S = S := rfl

/-- thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_two (S : ℤ) : chebyAdams 2 S = S ^ 2 - 2 := by
  simp [chebyAdams]; ring

/-- thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_three (S : ℤ) : chebyAdams 3 S = S ^ 3 - 3 * S := by
  simp [chebyAdams]; ring

private theorem chebyAdams_succ_succ (n : ℕ) (S : ℤ) :
    chebyAdams (n + 2) S = S * chebyAdams (n + 1) S - chebyAdams n S :=
  rfl

/-- Product-to-sum identity for Chebyshev-Adams polynomials:
    C_{a+n}(S) · C_n(S) = C_{a+2n}(S) + C_a(S).
    Proven by two-step induction on n. -/
private theorem chebyAdams_product_sum (S : ℤ) :
    ∀ n a, chebyAdams (a + n) S * chebyAdams n S =
      chebyAdams (a + 2 * n) S + chebyAdams a S := by
  suffices h : ∀ n, (∀ a, chebyAdams (a + n) S * chebyAdams n S =
      chebyAdams (a + 2 * n) S + chebyAdams a S) ∧
    (∀ a, chebyAdams (a + (n + 1)) S * chebyAdams (n + 1) S =
      chebyAdams (a + 2 * (n + 1)) S + chebyAdams a S)
    from fun n a => (h n).1 a
  intro n
  induction n with
  | zero =>
    refine ⟨fun a => ?_, fun a => ?_⟩
    · -- n=0: C_a · 2 = C_a + C_a
      simp [chebyAdams]; ring
    · -- n=1: C_{a+1} · S = C_{a+2} + C_a
      rw [show a + (0 + 1) = a + 1 from by omega, show a + 2 * (0 + 1) = a + 1 + 1 from by omega]
      rw [chebyAdams_succ_succ a, chebyAdams_one]; ring
  | succ k ihk =>
    obtain ⟨ih_k, ih_k1⟩ := ihk
    refine ⟨ih_k1, fun a => ?_⟩
    -- P(k+2): C_{a+k+2} · C_{k+2} = C_{a+2k+4} + C_a
    -- C_{k+2} = S · C_{k+1} - C_k
    rw [chebyAdams_succ_succ k S]
    -- LHS = C_{a+k+2} · (S · C_{k+1} - C_k)
    -- Use ih_k1 at a+1: C_{a+1+k+1} · C_{k+1} = C_{a+1+2(k+1)} + C_{a+1}
    have h1 := ih_k1 (a + 1)
    rw [show a + 1 + (k + 1) = a + k + 2 from by omega,
        show a + 1 + 2 * (k + 1) = a + 2 * k + 3 from by omega] at h1
    -- Use ih_k at a+2: C_{a+2+k} · C_k = C_{a+2+2k} + C_{a+2}
    have h2 := ih_k (a + 2)
    rw [show a + 2 + k = a + k + 2 from by omega,
        show a + 2 + 2 * k = a + 2 * k + 2 from by omega] at h2
    -- Target: C_{a+2(k+2)} + C_a = C_{a+2k+4} + C_a
    rw [show a + 2 * (k + 1 + 1) = (a + 2 * k + 2) + 1 + 1 from by omega]
    rw [chebyAdams_succ_succ (a + 2 * k + 2)]
    rw [show (a + 2 * k + 2) + 1 = a + 2 * k + 3 from by omega]
    rw [show a + (k + 1 + 1) = a + k + 2 from by omega]
    -- Goal: C_{a+k+2} · (S · C_{k+1} - C_k) = S · C_{a+2k+3} - C_{a+2k+2} + C_a
    -- Distribute LHS
    have hdist : chebyAdams (a + k + 2) S * (S * chebyAdams (k + 1) S - chebyAdams k S) =
        S * (chebyAdams (a + k + 2) S * chebyAdams (k + 1) S) -
        chebyAdams (a + k + 2) S * chebyAdams k S := by ring
    rw [hdist, h1, h2, chebyAdams_succ_succ a S]
    ring

/-- Chebyshev shift identity: C_{a + 2n}(S) = C_n(S) · C_{a+n}(S) - C_a(S). -/
private theorem chebyAdams_shift (n : ℕ) (S : ℤ) (a : ℕ) :
    chebyAdams (a + 2 * n) S =
      chebyAdams n S * chebyAdams (a + n) S - chebyAdams a S := by
  linarith [chebyAdams_product_sum S n a]

/-- Semigroup law: C_{m·n}(S) = C_m(C_n(S)).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_mul (m n : ℕ) (S : ℤ) :
    chebyAdams (m * n) S = chebyAdams m (chebyAdams n S) := by
  induction m using Nat.strongRecOn with
  | ind m ihm =>
  match m with
  | 0 => simp
  | 1 => simp
  | m + 2 =>
    rw [show (m + 2) * n = m * n + 2 * n from by ring]
    rw [chebyAdams_shift n S (m * n)]
    rw [show m * n + n = (m + 1) * n from by ring]
    rw [ihm (m + 1) (by omega)]
    rw [ihm m (by omega)]
    rw [chebyAdams_succ_succ]

-- ══════════════════════════════════════════════════════════════
-- Phase R253: Chebyshev-Adams specializations and product formula
-- ══════════════════════════════════════════════════════════════

/-- C_n(2) = 2 for all n (r=1 specialization: T_n(1) = 1).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_two : ∀ n : ℕ, chebyAdams n 2 = 2
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by rw [chebyAdams_succ_succ]; linarith [chebyAdams_at_two n, chebyAdams_at_two (n + 1)]

/-- C_n(-2) = 2·(-1)^n for all n (r=-1 specialization).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_neg_two : ∀ n : ℕ, chebyAdams n (-2) = 2 * (-1 : ℤ) ^ n
  | 0 => by simp [chebyAdams]
  | 1 => by simp [chebyAdams]
  | n + 2 => by
    rw [chebyAdams_succ_succ]
    rw [chebyAdams_at_neg_two (n + 1), chebyAdams_at_neg_two n]
    ring

/-- Product-to-sum: C_m · C_n = C_{m+n} + C_{|m-n|} for m ≥ n.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_product_formula (m n : ℕ) (S : ℤ) (hmn : n ≤ m) :
    chebyAdams m S * chebyAdams n S =
      chebyAdams (m + n) S + chebyAdams (m - n) S := by
  have h := chebyAdams_product_sum S n (m - n)
  rw [show m - n + n = m from by omega, show m - n + 2 * n = m + n from by omega] at h
  linarith

/-- chebyAdams 4 explicit formula.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_four (S : ℤ) : chebyAdams 4 S = S ^ 4 - 4 * S ^ 2 + 2 := by
  simp [chebyAdams]; ring

/-- chebyAdams 5 explicit formula.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_five (S : ℤ) : chebyAdams 5 S = S ^ 5 - 5 * S ^ 3 + 5 * S := by
  simp [chebyAdams]; ring

/-- chebyAdams 6 explicit formula.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_six (S : ℤ) : chebyAdams 6 S = S ^ 6 - 6 * S ^ 4 + 9 * S ^ 2 - 2 := by
  simp [chebyAdams]; ring

/-- Chebyshev-Adams polynomial package.
    thm:discussion-chebyshev-witt-equivariance -/
theorem paper_chebyAdams_product_and_values :
    (∀ S : ℤ, chebyAdams 2 S = S ^ 2 - 2) ∧
    (∀ S : ℤ, chebyAdams 3 S = S ^ 3 - 3 * S) ∧
    (∀ S : ℤ, chebyAdams 4 S = S ^ 4 - 4 * S ^ 2 + 2) ∧
    (∀ S : ℤ, chebyAdams 5 S = S ^ 5 - 5 * S ^ 3 + 5 * S) ∧
    chebyAdams 2 3 = 7 ∧ chebyAdams 3 3 = 18 ∧ chebyAdams 4 3 = 47 :=
  ⟨chebyAdams_two, chebyAdams_three, chebyAdams_four, chebyAdams_five,
   by native_decide, by native_decide, by native_decide⟩

/-- Horizon boundary layer Fibonacci/Lucas audit.
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem paper_discussion_horizon_fibonacci_audit :
    (Nat.fib 2 * Nat.fib 4 + 1 = Nat.fib 3 ^ 2) ∧
    (Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1) ∧
    (Nat.fib 6 ∣ Nat.fib 12) ∧
    (Nat.gcd (Nat.fib 6) (Nat.fib 9) = Nat.fib (Nat.gcd 6 9)) := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R280: Chebyshev-Adams at S=1 and S=-1 periodicity
-- ══════════════════════════════════════════════════════════════

/-- Explicit values of Chebyshev-Adams at S=1 for one full period.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_one_values :
    chebyAdams 0 1 = 2 ∧ chebyAdams 1 1 = 1 ∧
    chebyAdams 2 1 = -1 ∧ chebyAdams 3 1 = -2 ∧
    chebyAdams 4 1 = -1 ∧ chebyAdams 5 1 = 1 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [chebyAdams]

/-- Chebyshev-Adams at S=1 has period 6: C(n+6, 1) = C(n, 1).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_one_period6 (n : ℕ) : chebyAdams (n + 6) 1 = chebyAdams n 1 := by
  -- Unfold 6 steps of the recurrence C(n+2,1) = 1·C(n+1,1) - C(n,1)
  have h1 : chebyAdams (n + 6) 1 = 1 * chebyAdams (n + 5) 1 - chebyAdams (n + 4) 1 := by
    rw [show n + 6 = (n + 4) + 2 from by omega]; exact chebyAdams_succ_succ (n + 4) 1
  have h2 : chebyAdams (n + 5) 1 = 1 * chebyAdams (n + 4) 1 - chebyAdams (n + 3) 1 := by
    rw [show n + 5 = (n + 3) + 2 from by omega]; exact chebyAdams_succ_succ (n + 3) 1
  have h3 : chebyAdams (n + 4) 1 = 1 * chebyAdams (n + 3) 1 - chebyAdams (n + 2) 1 := by
    rw [show n + 4 = (n + 2) + 2 from by omega]; exact chebyAdams_succ_succ (n + 2) 1
  have h4 : chebyAdams (n + 3) 1 = 1 * chebyAdams (n + 2) 1 - chebyAdams (n + 1) 1 := by
    rw [show n + 3 = (n + 1) + 2 from by omega]; exact chebyAdams_succ_succ (n + 1) 1
  have h5 : chebyAdams (n + 2) 1 = 1 * chebyAdams (n + 1) 1 - chebyAdams n 1 := by
    exact chebyAdams_succ_succ n 1
  linarith

/-- Explicit values of Chebyshev-Adams at S=-1.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_neg_one_values :
    chebyAdams 0 (-1) = 2 ∧ chebyAdams 1 (-1) = -1 ∧
    chebyAdams 2 (-1) = -1 := by
  refine ⟨rfl, rfl, ?_⟩; simp [chebyAdams]

/-- Chebyshev-Adams at S=-1 has period 3: C(n+3, -1) = C(n, -1).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_neg_one_period3 (n : ℕ) :
    chebyAdams (n + 3) (-1) = chebyAdams n (-1) := by
  -- Unfold 3 steps of the recurrence C(n+2,-1) = -C(n+1,-1) - C(n,-1)
  have h1 : chebyAdams (n + 3) (-1) = -1 * chebyAdams (n + 2) (-1) - chebyAdams (n + 1) (-1) := by
    rw [show n + 3 = (n + 1) + 2 from by omega]; exact chebyAdams_succ_succ (n + 1) (-1)
  have h2 : chebyAdams (n + 2) (-1) = -1 * chebyAdams (n + 1) (-1) - chebyAdams n (-1) := by
    exact chebyAdams_succ_succ n (-1)
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R286: Chebyshev-Adams at S=0 periodicity
-- ══════════════════════════════════════════════════════════════

/-- C(n+2, 0) = -C(n, 0). thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_zero_neg (n : ℕ) :
    chebyAdams (n + 2) 0 = -chebyAdams n 0 := by
  have : chebyAdams (n + 2) 0 = 0 * chebyAdams (n + 1) 0 - chebyAdams n 0 :=
    chebyAdams_succ_succ n 0
  linarith

/-- C(n+4, 0) = C(n, 0). thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_zero_period4 (n : ℕ) :
    chebyAdams (n + 4) 0 = chebyAdams n 0 := by
  rw [show n + 4 = (n + 2) + 2 from by omega, chebyAdams_at_zero_neg,
    chebyAdams_at_zero_neg, neg_neg]

/-- Explicit values: {2, 0, -2, 0}. thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_zero_values :
    chebyAdams 0 0 = 2 ∧ chebyAdams 1 0 = 0 ∧
    chebyAdams 2 0 = -2 ∧ chebyAdams 3 0 = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [chebyAdams]

/-- Complete special-value package. thm:discussion-chebyshev-witt-equivariance -/
theorem paper_chebyAdams_special_values_complete :
    (∀ n, chebyAdams n 2 = 2) ∧
    (∀ n, chebyAdams n (-2) = 2 * (-1) ^ n) ∧
    (∀ n, chebyAdams (n + 6) 1 = chebyAdams n 1) ∧
    (∀ n, chebyAdams (n + 3) (-1) = chebyAdams n (-1)) ∧
    (∀ n, chebyAdams (n + 4) 0 = chebyAdams n 0) :=
  ⟨chebyAdams_at_two, chebyAdams_at_neg_two, chebyAdams_at_one_period6,
   chebyAdams_at_neg_one_period3, chebyAdams_at_zero_period4⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R294: Chebyshev-Adams neg arg, C_7/C_8 explicit
-- ══════════════════════════════════════════════════════════════

/-- C_d(-S) = (-1)^d · C_d(S). thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_neg_arg : ∀ (d : ℕ) (S : ℤ),
    chebyAdams d (-S) = (-1) ^ d * chebyAdams d S
  | 0, S => by simp [chebyAdams]
  | 1, S => by simp [chebyAdams]
  | d + 2, S => by
    rw [chebyAdams_succ_succ d (-S), chebyAdams_neg_arg (d + 1) S, chebyAdams_neg_arg d S,
      chebyAdams_succ_succ d S]
    ring

/-- chebyAdams 7 explicit formula. thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_seven (S : ℤ) :
    chebyAdams 7 S = S ^ 7 - 7 * S ^ 5 + 14 * S ^ 3 - 7 * S := by
  simp [chebyAdams]; ring

/-- chebyAdams 8 explicit formula. thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_eight (S : ℤ) :
    chebyAdams 8 S = S ^ 8 - 8 * S ^ 6 + 20 * S ^ 4 - 16 * S ^ 2 + 2 := by
  simp [chebyAdams]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase R303: chebyAdams(n, 3) = lucasNum(2n)
-- ══════════════════════════════════════════════════════════════

open Omega.Zeta in
/-- Lucas(2n) satisfies the same recurrence as chebyAdams(n, 3).
    thm:zeta-syntax-trace-linear-recurrence -/
theorem lucasNum_even_recurrence (n : Nat) :
    Omega.Zeta.lucasNum (2 * n + 4) = 3 * Omega.Zeta.lucasNum (2 * n + 2) -
      Omega.Zeta.lucasNum (2 * n) := by
  have h1 := Omega.Zeta.lucasNum_succ_succ (2 * n)
  have h2 := Omega.Zeta.lucasNum_succ_succ (2 * n + 1)
  have h3 := Omega.Zeta.lucasNum_succ_succ (2 * n + 2)
  rw [show (2 * n) + 2 = 2 * n + 2 from rfl] at h1
  rw [show (2 * n + 1) + 2 = 2 * n + 3 from by omega,
      show (2 * n + 1) + 1 = 2 * n + 2 from by omega] at h2
  rw [show (2 * n + 2) + 2 = 2 * n + 4 from by omega,
      show (2 * n + 2) + 1 = 2 * n + 3 from by omega] at h3
  linarith

/-- chebyAdams(n, 3) = lucasNum(2*n).
    cor:discussion-ramanujan-half-dimension-collapse -/
theorem chebyAdams_at_three_eq_lucas_even (n : Nat) :
    chebyAdams n 3 = Omega.Zeta.lucasNum (2 * n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [chebyAdams, Omega.Zeta.lucasNum]
    | 1 => simp [chebyAdams, Omega.Zeta.lucasNum]
    | n + 2 =>
      rw [chebyAdams_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
      rw [show 2 * (n + 2) = 2 * n + 4 from by ring,
          show 2 * (n + 1) = 2 * n + 2 from by ring]
      have := lucasNum_even_recurrence n
      linarith

/-- Paper package.
    cor:discussion-ramanujan-half-dimension-collapse -/
theorem paper_chebyAdams_at_three_package :
    chebyAdams 0 3 = 2 ∧ chebyAdams 1 3 = 3 ∧
    chebyAdams 2 3 = 7 ∧ chebyAdams 3 3 = 18 ∧
    chebyAdams 4 3 = 47 ∧ chebyAdams 5 3 = 123 ∧
    (∀ n, chebyAdams n 3 = Omega.Zeta.lucasNum (2 * n)) := by
  refine ⟨by simp [chebyAdams], by simp [chebyAdams], ?_, ?_, ?_, ?_,
    chebyAdams_at_three_eq_lucas_even⟩
  all_goals rw [chebyAdams_at_three_eq_lucas_even]; simp [Omega.Zeta.lucasNum]

-- ══════════════════════════════════════════════════════════════
-- Phase R305: chebyAdams at S=-3 = alternating Lucas
-- ══════════════════════════════════════════════════════════════

/-- thm:zeta-syntax-trace-linear-recurrence -/
theorem chebyAdams_at_neg_three_eq_alt_lucas (n : Nat) :
    chebyAdams n (-3) = (-1) ^ n * Omega.Zeta.lucasNum (2 * n) := by
  rw [chebyAdams_neg_arg, chebyAdams_at_three_eq_lucas_even]

/-- thm:zeta-syntax-trace-linear-recurrence -/
theorem paper_chebyAdams_golden_mean_package :
    (∀ n, chebyAdams n 3 = Omega.Zeta.lucasNum (2 * n)) ∧
    (∀ n, chebyAdams n (-3) = (-1) ^ n * Omega.Zeta.lucasNum (2 * n)) ∧
    chebyAdams 0 3 = 2 ∧ chebyAdams 1 3 = 3 ∧
    chebyAdams 0 (-3) = 2 ∧ chebyAdams 1 (-3) = -3 := by
  exact ⟨chebyAdams_at_three_eq_lucas_even,
    chebyAdams_at_neg_three_eq_alt_lucas,
    by simp [chebyAdams], by simp [chebyAdams],
    by simp [chebyAdams], by simp [chebyAdams]⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R308: chebyAdams 9 + 10 explicit formula
-- ══════════════════════════════════════════════════════════════

/-- thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_nine (S : ℤ) :
    chebyAdams 9 S = S ^ 9 - 9 * S ^ 7 + 27 * S ^ 5 - 30 * S ^ 3 + 9 * S := by
  simp [chebyAdams]; ring

/-- thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_ten (S : ℤ) :
    chebyAdams 10 S = S ^ 10 - 10 * S ^ 8 + 35 * S ^ 6 - 50 * S ^ 4 + 25 * S ^ 2 - 2 := by
  simp [chebyAdams]; ring

/-- Paper package. thm:discussion-chebyshev-witt-equivariance -/
theorem paper_chebyAdams_nine_ten :
    chebyAdams 9 3 = 5778 ∧ chebyAdams 10 3 = 15127 ∧
    chebyAdams 9 (-3) = -5778 ∧ chebyAdams 10 (-3) = 15127 := by
  rw [chebyAdams_nine, chebyAdams_ten, chebyAdams_nine, chebyAdams_ten]; norm_num

-- ══════════════════════════════════════════════════════════════
-- Phase R311: chebyAdams Frobenius mod p
-- ══════════════════════════════════════════════════════════════

/-- Frobenius property for concrete instances.
    thm:discussion-chebyshev-witt-equivariance -/
theorem paper_chebyAdams_frobenius :
    chebyAdams 2 3 % 2 = 3 % 2 ∧
    chebyAdams 3 3 % 3 = 3 % 3 ∧
    chebyAdams 5 3 % 5 = 3 % 5 ∧
    chebyAdams 7 3 % 7 = 3 % 7 ∧
    chebyAdams 11 3 % 11 = 3 % 11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [chebyAdams_two]; norm_num
  · rw [chebyAdams_three]; norm_num
  · rw [chebyAdams_five]; norm_num
  · rw [chebyAdams_seven]; norm_num
  · simp [chebyAdams]

/-- Frobenius at S=0 and S=1.
    thm:discussion-chebyshev-witt-equivariance -/
theorem paper_chebyAdams_frobenius_zero_one :
    chebyAdams 2 0 % 2 = 0 % 2 ∧
    chebyAdams 3 0 % 3 = 0 % 3 ∧
    chebyAdams 5 0 % 5 = 0 % 5 ∧
    chebyAdams 2 1 % 2 = 1 % 2 ∧
    chebyAdams 3 1 % 3 = 1 % 3 ∧
    chebyAdams 5 1 % 5 = 1 % 5 := by
  simp [chebyAdams_two, chebyAdams_three, chebyAdams_five]

-- ══════════════════════════════════════════════════════════════
-- Phase R315: Dwork-Chebyshev package
-- ══════════════════════════════════════════════════════════════

/-- Double-angle formula: C_{2n}(S) = C_n(S² - 2).
    thm:discussion-completed-dwork-chebyshev -/
theorem chebyAdams_double (n : ℕ) (S : ℤ) :
    chebyAdams (2 * n) S = chebyAdams n (S ^ 2 - 2) := by
  rw [show 2 * n = n * 2 from by ring, chebyAdams_mul, chebyAdams_two]

/-- Triple-angle formula: C_{3n}(S) = C_n(S³ - 3S).
    thm:discussion-completed-dwork-chebyshev -/
theorem chebyAdams_triple (n : ℕ) (S : ℤ) :
    chebyAdams (3 * n) S = chebyAdams n (S ^ 3 - 3 * S) := by
  rw [show 3 * n = n * 3 from by ring, chebyAdams_mul, chebyAdams_three]

/-- Dwork congruence (exact form): C_{p^{k+1}}(S) = C_{p^k}(C_p(S)).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_pow_prime_compose (p k : ℕ) (S : ℤ) :
    chebyAdams (p ^ (k + 1)) S = chebyAdams (p ^ k) (chebyAdams p S) := by
  rw [pow_succ, chebyAdams_mul]

-- ══════════════════════════════════════════════════════════════
-- Phase R320: Chebyshev-Adams at S=4
-- ══════════════════════════════════════════════════════════════

/-- Recurrence for C_n(4): C_{n+2}(4) = 4·C_{n+1}(4) - C_n(4).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_four_recurrence (n : Nat) :
    chebyAdams (n + 2) 4 = 4 * chebyAdams (n + 1) 4 - chebyAdams n 4 := by
  rw [chebyAdams_succ_succ]

/-- Base values: C_0(4) = 2, C_1(4) = 4.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_four_base :
    chebyAdams 0 4 = 2 ∧ chebyAdams 1 4 = 4 := by
  simp [chebyAdams]

-- ══════════════════════════════════════════════════════════════
-- Phase R323: Chebyshev-Adams at S=5
-- ══════════════════════════════════════════════════════════════

/-- Recurrence for C_n(5): C_{n+2}(5) = 5·C_{n+1}(5) - C_n(5).
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_five_recurrence (n : Nat) :
    chebyAdams (n + 2) 5 = 5 * chebyAdams (n + 1) 5 - chebyAdams n 5 := by
  rw [chebyAdams_succ_succ]

/-- Base values: C_0(5) = 2, C_1(5) = 5.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_five_base :
    chebyAdams 0 5 = 2 ∧ chebyAdams 1 5 = 5 := by simp [chebyAdams]

/-- Concrete values: C_2(5) = 23, C_3(5) = 110, C_4(5) = 527.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_at_five_values :
    chebyAdams 2 5 = 23 ∧ chebyAdams 3 5 = 110 ∧ chebyAdams 4 5 = 527 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [chebyAdams]

-- ══════════════════════════════════════════════════════════════
-- Phase R326: Chebyshev-Adams squaring identities
-- ══════════════════════════════════════════════════════════════

/-- Squaring identity: C_n² = C_{2n} + 2.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_sq_eq (n : Nat) (S : ℤ) :
    chebyAdams n S * chebyAdams n S = chebyAdams (2 * n) S + 2 := by
  have h := chebyAdams_product_formula n n S (le_refl n)
  simp only [Nat.sub_self, chebyAdams_zero, show n + n = 2 * n from by omega] at h
  linarith

/-- Squaring minus two: C_n² - 2 = C_{2n}.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_sq_sub_two (n : Nat) (S : ℤ) :
    chebyAdams n S * chebyAdams n S - 2 = chebyAdams (2 * n) S := by
  linarith [chebyAdams_sq_eq n S]

-- ══════════════════════════════════════════════════════════════
-- Phase R330: Chebyshev-Adams Cassini identity
-- ══════════════════════════════════════════════════════════════

/-- Cassini identity for Chebyshev-Adams: C_n·C_{n+2} - C_{n+1}² = S² - 4.
    thm:discussion-chebyshev-witt-equivariance -/
theorem chebyAdams_cassini (n : Nat) (S : ℤ) :
    chebyAdams n S * chebyAdams (n + 2) S - chebyAdams (n + 1) S ^ 2 = S ^ 2 - 4 := by
  induction n with
  | zero => simp [chebyAdams]; ring
  | succ n ih =>
    set a := chebyAdams n S
    set b := chebyAdams (n + 1) S
    set c := chebyAdams (n + 2) S
    -- ih: a * c - b ^ 2 = S ^ 2 - 4
    -- hrec: c = S * b - a
    have hrec : c = S * b - a := chebyAdams_succ_succ n S
    -- C_{n+3} = S * c - b
    have h3 : chebyAdams (n + 3) S = S * c - b := chebyAdams_succ_succ (n + 1) S
    -- Goal: b * C_{n+3} - c ^ 2 = S ^ 2 - 4
    show b * chebyAdams (n + 1 + 2) S - chebyAdams (n + 1 + 1) S ^ 2 = S ^ 2 - 4
    rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega]
    rw [h3]
    change b * (S * c - b) - c ^ 2 = S ^ 2 - 4
    -- Substituting hrec: c = S*b - a into ih: a*c - b^2 = S^2 - 4
    -- gives a*(S*b-a) - b^2 = S^2-4, i.e., S*a*b - a^2 - b^2 = S^2-4
    -- Goal after expanding: S*b*c - b^2 - c^2 = S^2-4
    -- With c = S*b-a: S*b*(S*b-a) - b^2 - (S*b-a)^2 = S*a*b - a^2 - b^2 = S^2-4
    have key : b * (S * c - b) - c ^ 2 = a * c - b ^ 2 := by
      rw [hrec]; ring
    linarith

end Omega.Discussion
