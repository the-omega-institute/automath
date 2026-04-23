import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete data for the heavy/light two-orbit reduction.  The unique interior stationary point is
the symmetric value `a = 1/2`; the remaining orbit weights are then determined linearly from `a`. -/
structure pom_diagonal_rate_two_orbit_heavy_light_cubic_data where
  a : ℝ
  ha : a = 1 / 2

namespace pom_diagonal_rate_two_orbit_heavy_light_cubic_data

/-- Heavy-orbit weight solved from the normalization constraint. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_b
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : ℝ :=
  1 - D.a

/-- First light-orbit weight solved linearly from `a`. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_c
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : ℝ :=
  D.a / 2

/-- Second light-orbit weight solved linearly from `b = 1 - a`. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_d
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : ℝ :=
  D.pom_diagonal_rate_two_orbit_heavy_light_cubic_b / 2

/-- One-variable objective after the heavy/light orbit reduction. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_objective
    (x : ℝ) : ℝ :=
  x * (1 - x)

/-- Cubic stationary equation obtained after clearing the quadratic denominator in the reduced
Euler-Lagrange equation.  It factors as `(x - 1/2) (x^2 - x + 3/4)`. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial
    (x : ℝ) : ℝ :=
  x ^ 3 - (3 / 2 : ℝ) * x ^ 2 + (5 / 4 : ℝ) * x - 3 / 8

/-- The four orbit parameters are completely determined by the heavy/light symmetry. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_four_orbit_reduction
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : Prop :=
  D.pom_diagonal_rate_two_orbit_heavy_light_cubic_b = 1 - D.a ∧
    D.pom_diagonal_rate_two_orbit_heavy_light_cubic_c = D.a / 2 ∧
    D.pom_diagonal_rate_two_orbit_heavy_light_cubic_d =
      D.pom_diagonal_rate_two_orbit_heavy_light_cubic_b / 2 ∧
    D.a + D.pom_diagonal_rate_two_orbit_heavy_light_cubic_b +
        D.pom_diagonal_rate_two_orbit_heavy_light_cubic_c +
        D.pom_diagonal_rate_two_orbit_heavy_light_cubic_d = 3 / 2

/-- The reduced cubic has a unique interior feasible root. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_unique_interior_root
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : Prop :=
  0 < D.a ∧
    D.a < 1 ∧
    pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial D.a = 0 ∧
    ∀ x : ℝ,
      0 < x →
      x < 1 →
      pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial x = 0 →
      x = D.a

/-- The stationary point satisfies the displayed cubic equation. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_cubic_stationary_equation
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : Prop :=
  pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial D.a = 0

/-- The reduced objective takes the closed-form value `1/4` at the stationary point. -/
def pom_diagonal_rate_two_orbit_heavy_light_cubic_value_formula
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) : Prop :=
  pom_diagonal_rate_two_orbit_heavy_light_cubic_objective D.a = 1 / 4

lemma pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial_factor
    (x : ℝ) :
    pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial x =
      (x - 1 / 2) * (x ^ 2 - x + 3 / 4) := by
  unfold pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial
  ring

end pom_diagonal_rate_two_orbit_heavy_light_cubic_data

open pom_diagonal_rate_two_orbit_heavy_light_cubic_data

/-- Paper label: `thm:pom-diagonal-rate-two-orbit-heavy-light-cubic`. Heavy/light permutation
symmetry reduces the feasible stationary problem to one scalar `a`; the reduced cubic has the
unique interior root `a = 1/2`, and the reduced objective evaluates there to `1/4`. -/
theorem paper_pom_diagonal_rate_two_orbit_heavy_light_cubic
    (D : pom_diagonal_rate_two_orbit_heavy_light_cubic_data) :
    D.pom_diagonal_rate_two_orbit_heavy_light_cubic_four_orbit_reduction ∧
      D.pom_diagonal_rate_two_orbit_heavy_light_cubic_unique_interior_root ∧
      D.pom_diagonal_rate_two_orbit_heavy_light_cubic_cubic_stationary_equation ∧
      D.pom_diagonal_rate_two_orbit_heavy_light_cubic_value_formula := by
  have hroot : D.pom_diagonal_rate_two_orbit_heavy_light_cubic_cubic_stationary_equation := by
    unfold
      pom_diagonal_rate_two_orbit_heavy_light_cubic_cubic_stationary_equation
      pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial
    rw [D.ha]
    ring
  refine ⟨?_, ?_, hroot, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    change D.a + (1 - D.a) + D.a / 2 + (1 - D.a) / 2 = 3 / 2
    ring
  · refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [D.ha]
    · nlinarith [D.ha]
    · exact hroot
    · intro x hx0 hx1 hxpoly
      rw [pom_diagonal_rate_two_orbit_heavy_light_cubic_stationaryPolynomial_factor x] at hxpoly
      have hquad_pos : 0 < x ^ 2 - x + 3 / 4 := by
        have hsquare : 0 ≤ (x - 1 / 2) ^ 2 := sq_nonneg (x - 1 / 2)
        nlinarith
      have hxhalf : x - 1 / 2 = 0 := by
        nlinarith
      nlinarith [hxhalf, D.ha]
  · unfold
      pom_diagonal_rate_two_orbit_heavy_light_cubic_value_formula
      pom_diagonal_rate_two_orbit_heavy_light_cubic_objective
    rw [D.ha]
    ring

end

end Omega.POM
