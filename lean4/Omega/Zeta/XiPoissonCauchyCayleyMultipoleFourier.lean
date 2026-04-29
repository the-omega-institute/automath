import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Real parameters for the Cayley--Poisson algebraic kernel calculation. -/
structure xi_poisson_cauchy_cayley_multipole_fourier_data where
  y : ℝ
  a : ℝ
  t : ℝ

/-- Cauchy kernel ratio after translating by the barycenter. -/
noncomputable def xi_poisson_cauchy_cayley_multipole_fourier_cauchy_ratio
    (y a t : ℝ) : ℝ :=
  (y ^ 2 + t ^ 2) / ((y - a) ^ 2 + t ^ 2)

/-- The real Poisson kernel written in Cayley and multipole coordinates. -/
noncomputable def xi_poisson_cauchy_cayley_multipole_fourier_poisson_ratio
    (y a t : ℝ) : ℝ :=
  (4 * t ^ 2 / (a ^ 2 + 4 * t ^ 2)) /
    (4 * t ^ 2 * ((y - a) ^ 2 + t ^ 2) / ((y ^ 2 + t ^ 2) * (a ^ 2 + 4 * t ^ 2)))

/-- Fourier coefficients of the scalar Poisson expansion attached to the multipole variable. -/
noncomputable def xi_poisson_cauchy_cayley_multipole_fourier_coeff
    (w : ℝ) : ℤ → ℝ
  | Int.ofNat 0 => 1
  | Int.ofNat (k + 1) => w ^ (k + 1)
  | Int.negSucc k => w ^ (k + 1)

/-- Concrete algebraic and coefficient form of the Cayley--Poisson multipole expansion. -/
def xi_poisson_cauchy_cayley_multipole_fourier_statement
    (D : xi_poisson_cauchy_cayley_multipole_fourier_data) : Prop :=
  D.t ≠ 0 →
    xi_poisson_cauchy_cayley_multipole_fourier_poisson_ratio D.y D.a D.t =
        xi_poisson_cauchy_cayley_multipole_fourier_cauchy_ratio D.y D.a D.t ∧
      (∀ k : ℕ,
        xi_poisson_cauchy_cayley_multipole_fourier_coeff
            (D.a / (D.a + 2 * D.t)) (Int.ofNat (k + 1)) =
          (D.a / (D.a + 2 * D.t)) ^ (k + 1)) ∧
      (∀ k : ℕ,
        xi_poisson_cauchy_cayley_multipole_fourier_coeff
            (D.a / (D.a + 2 * D.t)) (Int.negSucc k) =
          (D.a / (D.a + 2 * D.t)) ^ (k + 1))

/-- Paper label: `prop:xi-poisson-cauchy-cayley-multipole-fourier`. -/
theorem paper_xi_poisson_cauchy_cayley_multipole_fourier
    (D : xi_poisson_cauchy_cayley_multipole_fourier_data) :
    xi_poisson_cauchy_cayley_multipole_fourier_statement D := by
  intro ht
  constructor
  · have ht_sq_pos : 0 < D.t ^ 2 := sq_pos_of_ne_zero ht
    have h4t : 4 * D.t ^ 2 ≠ 0 := by nlinarith
    have hy : D.y ^ 2 + D.t ^ 2 ≠ 0 := by
      have hy_nonneg : 0 ≤ D.y ^ 2 := sq_nonneg D.y
      nlinarith
    have ha : D.a ^ 2 + 4 * D.t ^ 2 ≠ 0 := by
      have ha_nonneg : 0 ≤ D.a ^ 2 := sq_nonneg D.a
      nlinarith
    have hya : (D.y - D.a) ^ 2 + D.t ^ 2 ≠ 0 := by
      have hya_nonneg : 0 ≤ (D.y - D.a) ^ 2 := sq_nonneg (D.y - D.a)
      nlinarith
    rw [xi_poisson_cauchy_cayley_multipole_fourier_poisson_ratio,
      xi_poisson_cauchy_cayley_multipole_fourier_cauchy_ratio]
    field_simp [h4t, hy, ha, hya]
  · constructor <;> intro k <;> rfl

end Omega.Zeta
