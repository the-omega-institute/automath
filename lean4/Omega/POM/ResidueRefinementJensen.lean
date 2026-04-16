import Mathlib.Tactic

/-! ### Subdivision moment bounds (Jensen / convexity)

For any non-negative reals (d_i)_{i=1}^P with Σ d_i = d and any q > 1:

  P^{1-q} · d^q  ≤  Σ d_i^q  ≤  d^q.

The right bound is power-mean monotonicity; the left is Jensen's inequality
applied to the convex function t ↦ t^q.

lem:pom-residue-refinement-jensen -/

namespace Omega.POM

open Finset

/-- Jensen lower bound for q = 2: n · Σ d_i² ≥ (Σ d_i)².
    This is exactly the Cauchy-Schwarz inequality for the counting measure.
    lem:pom-residue-refinement-jensen -/
theorem subdivision_moment_lower_q2 {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    (n : ℤ) * ∑ i : Fin n, d i ^ 2 ≥ (∑ i : Fin n, d i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    set a := d 0
    set S := ∑ i : Fin n, d (Fin.succ i)
    set S2 := ∑ i : Fin n, d (Fin.succ i) ^ 2
    have hih : (n : ℤ) * S2 ≥ S ^ 2 := ih (d ∘ Fin.succ) (fun i => hd _)
    -- (n+1)(a² + S2) ≥ (a + S)²
    -- Expanding: n*a² + a² + n*S2 + S2 ≥ a² + 2aS + S²
    -- i.e. n*a² + n*S2 + S2 ≥ 2aS + S²
    -- Since n*S2 ≥ S², suffices n*a² + S2 ≥ 2aS
    -- This follows from (a√n - S/√n)² ≥ 0, but more directly:
    -- n*a² + S2 ≥ n*a² + S²/n ≥ 2aS (AM-GM). However in ℤ:
    -- We need: (n+1)(a² + S2) ≥ (a + S)²
    -- Rewrite as: n*a² + a² + n*S2 + S2 ≥ a² + 2*a*S + S²
    -- Cancel a²: n*a² + n*S2 + S2 ≥ 2*a*S + S²
    -- Since n*S2 ≥ S², suffices: n*a² + S2 ≥ 2*a*S
    have key : n * a ^ 2 + S2 ≥ 2 * a * S := by
      -- From hih: n*S2 ≥ S², so S2 ≥ S²/n (when n > 0)
      -- And n*a² + S²/n ≥ 2*|a|*|S| (AM-GM)
      -- But let's just provide (n*a - S)² + n*(n*S2 - S²) ≥ 0 as a certificate
      -- Expand: n²*a² - 2*n*a*S + S² + n²*S2 - n*S² ≥ 0
      -- Hmm, this is n*(n*a² + n*S2 - 2*a*S) + (S² - n*S²) + ... wrong direction
      -- Alternative: multiply hih by a² to get n*a²*S2 ≥ a²*S², but degree 4
      -- Let's try: have (n*a² - 2*a*S + S2) ≥ 0
      -- This is what we want. Add the certificate n*(S2 - 2*a*S/n + a²/... )
      -- Actually the simplest: note 2*a*S ≤ n*a² + S²/n ≤ n*a² + S2
      -- since S²/n ≤ S2 from hih (when n ≥ 1). When n = 0, S = 0.
      by_cases hn : n = 0
      · subst hn; simp at hih
        have hS2 : 0 ≤ S2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
        rw [hih]; simp; linarith
      · -- n ≥ 1, so from hih: S² ≤ n * S2
        -- We need n*a² + S2 ≥ 2*a*S
        -- Observe: (n*a - S)² = n²*a² - 2*n*a*S + S² ≥ 0
        -- So n²*a² + S² ≥ 2*n*a*S, i.e. n*a² + S²/n ≥ 2*a*S (divide by n)
        -- But S²/n ≤ S2 from hih. So n*a² + S2 ≥ n*a² + S²/n ≥ 2*a*S
        -- In ℤ we can't divide. Instead:
        -- From (n*a - S)² ≥ 0: n²*a² + S² ≥ 2*n*a*S
        -- From hih: n*S2 ≥ S²
        -- So n²*a² + n*S2 ≥ n²*a² + S² ≥ 2*n*a*S
        -- So n*(n*a² + S2) ≥ 2*n*a*S
        -- Since n ≥ 1: n*a² + S2 ≥ 2*a*S
        have hn' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have h1 : (n : ℤ) * ((n : ℤ) * a ^ 2 + S2) ≥ 2 * (n : ℤ) * a * S := by
          nlinarith [sq_nonneg ((n : ℤ) * a - S)]
        have h2 : (n : ℤ) * a ^ 2 + S2 ≥ 2 * a * S := by
          by_contra h
          push_neg at h
          have : (n : ℤ) * ((n : ℤ) * a ^ 2 + S2) < (n : ℤ) * (2 * a * S) :=
            Int.mul_lt_mul_of_pos_left h hn'
          linarith
        exact h2
    -- (n+1)(a² + S2) ≥ (a+S)² follows from key + hih
    have cast_eq : (↑(n + 1) : ℤ) = ↑n + 1 := by push_cast; ring
    rw [cast_eq]
    have expand1 : (↑n + 1) * (a ^ 2 + S2) =
        ↑n * a ^ 2 + a ^ 2 + ↑n * S2 + S2 := by ring
    have expand2 : (a + S) ^ 2 = a ^ 2 + 2 * a * S + S ^ 2 := by ring
    linarith

/-- Upper bound for q = 2: Σ d_i² ≤ (Σ d_i)² since cross-terms are nonneg.
    lem:pom-residue-refinement-jensen -/
theorem subdivision_moment_upper_q2 {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    ∑ i : Fin n, d i ^ 2 ≤ (∑ i : Fin n, d i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    set a := d 0
    set S := ∑ i : Fin n, d (Fin.succ i)
    set S2 := ∑ i : Fin n, d (Fin.succ i) ^ 2
    have hih : S2 ≤ S ^ 2 := ih (d ∘ Fin.succ) (fun i => hd _)
    have ha : 0 ≤ a := hd 0
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hd _)
    nlinarith [sq_nonneg (a - S)]

/-- Combined Jensen bounds for q=2.
    (Σ d_i)² ≤ P · Σ d_i² and Σ d_i² ≤ (Σ d_i)².
    lem:pom-residue-refinement-jensen -/
theorem paper_pom_residue_refinement_jensen_q2 {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i : Fin n, d i) ^ 2 ≤ (n : ℤ) * ∑ i : Fin n, d i ^ 2 ∧
    ∑ i : Fin n, d i ^ 2 ≤ (∑ i : Fin n, d i) ^ 2 :=
  ⟨subdivision_moment_lower_q2 d hd, subdivision_moment_upper_q2 d hd⟩

/-- Nat version of the lower bound: n · Σ d_i² ≥ (Σ d_i)².
    lem:pom-residue-refinement-jensen -/
theorem subdivision_moment_lower_q2_nat {n : ℕ} (d : Fin n → ℕ) :
    n * ∑ i : Fin n, d i ^ 2 ≥ (∑ i : Fin n, d i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    set a := d 0
    set S := ∑ i : Fin n, d (Fin.succ i)
    set S2 := ∑ i : Fin n, d (Fin.succ i) ^ 2
    have hih : n * S2 ≥ S ^ 2 := ih (d ∘ Fin.succ)
    -- Work in ℤ to avoid natural subtraction issues
    suffices h : (n + 1 : ℤ) * ((a : ℤ) ^ 2 + (S2 : ℤ)) ≥ ((a : ℤ) + (S : ℤ)) ^ 2 by
      exact_mod_cast h
    -- Key: n*a² + S2 ≥ 2*a*S
    have hih_z : (S : ℤ) ^ 2 ≤ (n : ℤ) * (S2 : ℤ) := by exact_mod_cast hih
    have key : (n : ℤ) * (a : ℤ) ^ 2 + (S2 : ℤ) ≥ 2 * (a : ℤ) * (S : ℤ) := by
      by_cases hn : n = 0
      · subst hn
        have hS_sq : (S : ℤ) ^ 2 ≤ 0 := by linarith [hih_z]
        have hS0 : (S : ℤ) = 0 := by nlinarith [sq_nonneg (S : ℤ)]
        rw [hS0]; simp
      · have hn' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have step1 : (n : ℤ) * ((n : ℤ) * (a : ℤ) ^ 2 + (S2 : ℤ)) ≥
            2 * (n : ℤ) * (a : ℤ) * (S : ℤ) := by
          nlinarith [sq_nonneg ((n : ℤ) * (a : ℤ) - (S : ℤ))]
        by_contra h; push_neg at h
        linarith [Int.mul_lt_mul_of_pos_left h hn']
    linarith [sq_nonneg ((a : ℤ) - (S : ℤ))]

/-- Seeds for Jensen bounds: P=2, d=(2,3).
    Lower: 5² = 25 ≤ 2·(4+9) = 26.
    Upper: 4+9 = 13 ≤ 25 = 5².
    lem:pom-residue-refinement-jensen -/
theorem subdivision_moment_jensen_seeds :
    (2 + 3) ^ 2 ≤ 2 * (2 ^ 2 + 3 ^ 2) ∧
    (2 : ℕ) ^ 2 + 3 ^ 2 ≤ (2 + 3) ^ 2 := by omega

/-- Seeds for pressure reduction: P=3, equal d_i=4, d=12, q=2.
    lem:pom-residue-refinement-jensen -/
theorem subdivision_moment_jensen_equal_split_seed :
    (12 : ℕ) ^ 2 = 3 * (4 ^ 2 + 4 ^ 2 + 4 ^ 2) ∧
    (4 : ℕ) ^ 2 + 4 ^ 2 + 4 ^ 2 ≤ 12 ^ 2 := by omega

end Omega.POM
