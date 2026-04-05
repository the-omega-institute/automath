import Mathlib.Tactic

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

end Omega.Discussion
