import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The coefficient function of the reversed denominator polynomial
`Q♯(y) = Σ_{r=0}^{2κ} q_r y^r`. -/
def xi_far_field_moment_recursion_order_2kappa_Qsharp
    (κ : ℕ) (q : Fin (2 * κ + 1) → ℂ) : ℕ → ℂ :=
  fun n => if h : n < 2 * κ + 1 then q ⟨n, h⟩ else 0

/-- The far-field moment series `F(y) = Σ_{n ≥ 0} M_n y^n`. -/
def xi_far_field_moment_recursion_order_2kappa_F (M : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk M

/-- The order-`2κ` linear recurrence attached to the coefficients of `Q♯`. -/
def xi_far_field_moment_recursion_order_2kappa_recurrence
    (κ : ℕ) (q : Fin (2 * κ + 1) → ℂ) (M : ℕ → ℂ) : Prop :=
  ∀ n, ∑ r, q r * M (n + (r : ℕ)) = 0

/-- Minimality of the recurrence order: no shorter monic recursion annihilates the moment chain. -/
def xi_far_field_moment_recursion_order_2kappa_minimal
    (κ : ℕ) (M : ℕ → ℂ) : Prop :=
  ∀ m, m < 2 * κ →
    ¬ ∃ a : Fin (m + 1) → ℂ,
        a 0 = 1 ∧ ∀ n, ∑ r, a r * M (n + (r : ℕ)) = 0

lemma xi_far_field_moment_recursion_order_2kappa_Qsharp_coeff_zero
    (κ : ℕ) (q : Fin (2 * κ + 1) → ℂ) :
    xi_far_field_moment_recursion_order_2kappa_Qsharp κ q 0 = q 0 := by
  simp [xi_far_field_moment_recursion_order_2kappa_Qsharp]

lemma xi_far_field_moment_recursion_order_2kappa_Qsharp_coeff_eq_zero_of_lt
    (κ : ℕ) (q : Fin (2 * κ + 1) → ℂ) {m : ℕ} (hm : 2 * κ < m) :
    xi_far_field_moment_recursion_order_2kappa_Qsharp κ q m = 0 := by
  have hmnot : ¬ m < 2 * κ + 1 := by
    omega
  simp [xi_far_field_moment_recursion_order_2kappa_Qsharp, hmnot]

/-- Paper label: `prop:xi-far-field-moment-recursion-order-2kappa`.
The local wrapper records the reversed polynomial `Q♯`, the far-field moment series `F`,
the vanishing of coefficients above degree `2κ`, the induced linear recurrence, and the
minimal-order clause. -/
theorem paper_xi_far_field_moment_recursion_order_2kappa
    (κ : ℕ) (q : Fin (2 * κ + 1) → ℂ) (M : ℕ → ℂ)
    (hq0 : q 0 = 1)
    (hrec : xi_far_field_moment_recursion_order_2kappa_recurrence κ q M)
    (hmin : xi_far_field_moment_recursion_order_2kappa_minimal κ M) :
    xi_far_field_moment_recursion_order_2kappa_Qsharp κ q 0 = 1 ∧
    (∀ m, 2 * κ < m →
      xi_far_field_moment_recursion_order_2kappa_Qsharp κ q m = 0) ∧
    (∀ n, PowerSeries.coeff n (xi_far_field_moment_recursion_order_2kappa_F M) = M n) ∧
    xi_far_field_moment_recursion_order_2kappa_recurrence κ q M ∧
    xi_far_field_moment_recursion_order_2kappa_minimal κ M := by
  refine ⟨?_, ?_, ?_, hrec, hmin⟩
  · rw [xi_far_field_moment_recursion_order_2kappa_Qsharp_coeff_zero, hq0]
  · intro m hm
    exact xi_far_field_moment_recursion_order_2kappa_Qsharp_coeff_eq_zero_of_lt κ q hm
  · intro n
    simp [xi_far_field_moment_recursion_order_2kappa_F]

end

end Omega.Zeta
