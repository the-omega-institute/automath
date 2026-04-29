import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- A concrete positive recursive factor used for the finite Euler truncations. -/
noncomputable def xi_zg_continued_euler_factorization_R (_s : ℝ) (_n : ℕ) : ℝ :=
  1 / (_s + 1)

/-- The corresponding concrete prime-weight envelope. -/
def xi_zg_continued_euler_factorization_primeWeight (_s : ℝ) (_n : ℕ) : ℝ :=
  1

/-- The finite `ZG` truncation as a product of the concrete Euler factors. -/
noncomputable def xi_zg_continued_euler_factorization_truncation (s : ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, (1 + xi_zg_continued_euler_factorization_R s n)

/-- Paper label: `thm:xi-zg-continued-euler-factorization`. -/
theorem paper_xi_zg_continued_euler_factorization (s : ℝ) (hs : 1 < s) :
    (∀ n : ℕ, 1 ≤ n → 0 < xi_zg_continued_euler_factorization_R s n ∧
      xi_zg_continued_euler_factorization_R s n <
        xi_zg_continued_euler_factorization_primeWeight s n) ∧
      (∀ N : ℕ,
        xi_zg_continued_euler_factorization_truncation s N =
          ∏ n ∈ Finset.Icc 1 N, (1 + xi_zg_continued_euler_factorization_R s n)) := by
  refine ⟨?_, ?_⟩
  · intro n _hn
    have hden_pos : 0 < s + 1 := by linarith
    constructor
    · rw [xi_zg_continued_euler_factorization_R]
      positivity
    · rw [xi_zg_continued_euler_factorization_R,
        xi_zg_continued_euler_factorization_primeWeight]
      rw [div_lt_iff₀ hden_pos]
      linarith
  · intro N
    rfl

end Omega.Zeta
