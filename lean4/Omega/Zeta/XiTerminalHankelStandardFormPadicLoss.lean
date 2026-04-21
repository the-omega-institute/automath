import Mathlib.Tactic

namespace Omega.Zeta

/-- In the `d = 1` Hankel normal form, the leading determinant is just the scalar `p^s`. -/
noncomputable def xiTerminalHankelDet (p s : ℕ) : ℚ :=
  (p : ℚ) ^ s

/-- In the scalar Cramer formula, the adjugate numerator is exactly the shifted Hankel entry. -/
noncomputable def xiTerminalHankelAdjugateNumerator (u : ℚ) : ℚ :=
  u

/-- The scalar Hankel standard form `A = H₀⁻¹ H₁`. -/
noncomputable def xiTerminalHankelStandardForm (p s : ℕ) (u : ℚ) : ℚ :=
  xiTerminalHankelAdjugateNumerator u / xiTerminalHankelDet p s

/-- In the terminal `d = 1` Hankel block, dividing by `det(H₀) = p^s` loses exactly `s`
digits of `p`-adic precision, and a unit numerator perturbation of size `p^E` produces the sharp
output perturbation `p^(E-s)`.
    thm:xi-terminal-hankel-standard-form-padic-loss -/
theorem paper_xi_terminal_hankel_standard_form_padic_loss
    (p s E : ℕ) (hp : Nat.Prime p) (hsE : s ≤ E) :
    xiTerminalHankelStandardForm p s 1 =
      xiTerminalHankelAdjugateNumerator 1 / xiTerminalHankelDet p s ∧
      xiTerminalHankelStandardForm p s (1 + (p : ℚ) ^ E) -
          xiTerminalHankelStandardForm p s 1 =
        (p : ℚ) ^ (E - s) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  refine ⟨rfl, ?_⟩
  rcases Nat.exists_eq_add_of_le hsE with ⟨k, rfl⟩
  unfold xiTerminalHankelStandardForm xiTerminalHankelAdjugateNumerator xiTerminalHankelDet
  calc
    ((1 : ℚ) + (p : ℚ) ^ (s + k)) / (p : ℚ) ^ s - 1 / (p : ℚ) ^ s
        = (p : ℚ) ^ (s + k) / (p : ℚ) ^ s := by ring
    _ = (((p : ℚ) ^ s) * (p : ℚ) ^ k) / (p : ℚ) ^ s := by rw [pow_add]
    _ = (p : ℚ) ^ k := by
          field_simp [hpq]
    _ = (p : ℚ) ^ (s + k - s) := by simp

end Omega.Zeta
