import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The two-scale binomial transport map `F(z) = α z^m + β z^n`. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_binomialMap
    (m n : ℕ) (α β z : ℂ) : ℂ :=
  α * z ^ m + β * z ^ n

/-- The formal derivative, written in the factorized form used for the critical equation. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative
    (m n : ℕ) (α β z : ℂ) : ℂ :=
  if n = 0 then
    (m : ℂ) * α * z ^ (m - 1)
  else
    z ^ (n - 1) * ((m : ℂ) * α * z ^ (m - n) + (n : ℂ) * β)

/-- The algebraic critical equation for the positive-`n` case. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalEquationSet
    (m n : ℕ) (α β z : ℂ) : Prop :=
  z ^ (m - n) = -((n : ℂ) * β) / ((m : ℂ) * α)

/-- Nonzero critical points of the two-scale transport. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalSet
    (m n : ℕ) (α β z : ℂ) : Prop :=
  z ≠ 0 ∧
    xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative
      m n α β z = 0

/-- If `n = 0`, the nonzero critical set is empty. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_n_eq_zero_emptyCritical
    (m n : ℕ) (α β : ℂ) : Prop :=
  n = 0 →
    ∀ z : ℂ,
      ¬ xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalSet m n α β z

/-- If `1 ≤ n < m`, criticality is equivalent to the displayed binomial equation. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_n_criticalEquation
    (m n : ℕ) (α β : ℂ) : Prop :=
  1 ≤ n →
    ∀ z : ℂ,
      z ≠ 0 →
        (xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative
              m n α β z = 0 ↔
            xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalEquationSet
              m n α β z)

/-- All positive-`n` critical points have the same `(m-n)`-power, hence the same algebraic
radius datum. -/
def xi_time_part62d_two_scale_binomial_transport_singular_circle_sameRadius
    (m n : ℕ) (α β : ℂ) : Prop :=
  1 ≤ n →
    ∀ z w : ℂ,
      xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalSet m n α β z →
        xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalSet m n α β w →
          z ^ (m - n) = w ^ (m - n)

lemma xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_iff
    {m n : ℕ} {α β z : ℂ} (hmn : n < m) (hα : α ≠ 0) (hn : 1 ≤ n) (hz : z ≠ 0) :
    (xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative
          m n α β z = 0 ↔
        xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalEquationSet
          m n α β z) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hmpos : 0 < m := by omega
  have hmC : (m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hmpos)
  have hden : (m : ℂ) * α ≠ 0 := mul_ne_zero hmC hα
  have hzpow : z ^ (n - 1) ≠ 0 := pow_ne_zero _ hz
  constructor
  · intro hcrit
    have hbracket :
        (m : ℂ) * α * z ^ (m - n) + (n : ℂ) * β = 0 := by
      have hprod :
          z ^ (n - 1) * ((m : ℂ) * α * z ^ (m - n) + (n : ℂ) * β) = 0 := by
        simpa [xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative,
          hn0] using hcrit
      exact (mul_eq_zero.mp hprod).resolve_left hzpow
    have hmul : (m : ℂ) * α * z ^ (m - n) = -((n : ℂ) * β) := by
      rw [add_eq_zero_iff_eq_neg] at hbracket
      exact hbracket
    unfold xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalEquationSet
    calc
      z ^ (m - n) = ((m : ℂ) * α * z ^ (m - n)) / ((m : ℂ) * α) := by
        field_simp [hden]
      _ = -((n : ℂ) * β) / ((m : ℂ) * α) := by rw [hmul]
  · intro heq
    have hbracket :
        (m : ℂ) * α * z ^ (m - n) + (n : ℂ) * β = 0 := by
      unfold xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalEquationSet at heq
      rw [heq]
      field_simp [hden]
      ring
    have hprod :
        z ^ (n - 1) * ((m : ℂ) * α * z ^ (m - n) + (n : ℂ) * β) = 0 := by
      rw [hbracket, mul_zero]
    simpa [xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative, hn0]
      using hprod

/-- Paper label: `thm:xi-time-part62d-two-scale-binomial-transport-singular-circle`. -/
theorem paper_xi_time_part62d_two_scale_binomial_transport_singular_circle
    (m n : ℕ) (α β : ℂ) (hmn : n < m) (hα : α ≠ 0) (_hβ : β ≠ 0) :
    xi_time_part62d_two_scale_binomial_transport_singular_circle_n_eq_zero_emptyCritical
        m n α β ∧
      xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_n_criticalEquation
        m n α β ∧
        xi_time_part62d_two_scale_binomial_transport_singular_circle_sameRadius m n α β := by
  refine ⟨?_, ?_, ?_⟩
  · intro hn0 z hcrit
    rcases hcrit with ⟨hz, hderiv⟩
    have hmpos : 0 < m := by omega
    have hmC : (m : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hmpos)
    have hzpow : z ^ (m - 1) ≠ 0 := pow_ne_zero _ hz
    have hne : (m : ℂ) * α * z ^ (m - 1) ≠ 0 := mul_ne_zero (mul_ne_zero hmC hα) hzpow
    exact hne (by
      simpa [xi_time_part62d_two_scale_binomial_transport_singular_circle_criticalSet,
        xi_time_part62d_two_scale_binomial_transport_singular_circle_formalDerivative, hn0]
        using hderiv)
  · intro hn z hz
    exact xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_iff hmn hα hn hz
  · intro hn z w hzcrit hwcrit
    rcases hzcrit with ⟨hz, hzd⟩
    rcases hwcrit with ⟨hw, hwd⟩
    have hzEq :=
      (xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_iff
        hmn hα hn hz).mp hzd
    have hwEq :=
      (xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_iff
        hmn hα hn hw).mp hwd
    exact hzEq.trans hwEq.symm

end Omega.Zeta
