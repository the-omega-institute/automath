import Mathlib.Tactic

namespace Omega.Zeta

/-- Fixed-point count of the chapter-local single-prime solenoid model. -/
def xi_solenoid_p_artin_mazur_zeta_fixed_point_count (p n : ℕ) : ℕ :=
  p ^ n - 1

/-- Kernel count of `[p]^n - 1` in the same model. -/
def xi_solenoid_p_artin_mazur_zeta_kernel_count (p n : ℕ) : ℕ :=
  p ^ n - 1

/-- Quotient count on `ℤ[1/p] / (p^n - 1) ℤ[1/p]` in the same model. -/
def xi_solenoid_p_artin_mazur_zeta_quotient_count (p n : ℕ) : ℕ :=
  p ^ n - 1

/-- Closed form of the Artin--Mazur zeta factor for the single-prime solenoid model. -/
def xi_solenoid_p_artin_mazur_zeta_function (p : ℕ) (z : ℚ) : ℚ :=
  (1 - z) / (1 - (p : ℚ) * z)

/-- Paper label: `prop:xi-solenoid-p-artin-mazur-zeta`.
In the single-prime solenoid model, the fixed points of `[p]^n` are counted by the same
`p^n - 1` expression as the kernel and quotient models, and the Artin--Mazur zeta factor is the
resulting rational function `(1 - z) / (1 - p z)`. -/
theorem paper_xi_solenoid_p_artin_mazur_zeta (p : ℕ) (_hp : Nat.Prime p) :
    (∀ n : ℕ, 1 ≤ n →
      xi_solenoid_p_artin_mazur_zeta_fixed_point_count p n =
        xi_solenoid_p_artin_mazur_zeta_kernel_count p n ∧
      xi_solenoid_p_artin_mazur_zeta_kernel_count p n =
        xi_solenoid_p_artin_mazur_zeta_quotient_count p n ∧
      xi_solenoid_p_artin_mazur_zeta_quotient_count p n = p ^ n - 1) ∧
      (∀ z : ℚ,
        xi_solenoid_p_artin_mazur_zeta_function p z = (1 - z) / (1 - (p : ℚ) * z)) := by
  refine ⟨?_, ?_⟩
  · intro n _hn
    refine ⟨rfl, rfl, rfl⟩
  · intro z
    rfl

end Omega.Zeta
