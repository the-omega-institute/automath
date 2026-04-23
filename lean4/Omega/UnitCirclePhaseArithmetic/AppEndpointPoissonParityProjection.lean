import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The translated endpoint profile `g(θ) = f(π + θ)`, represented on the integer model by a unit
shift. -/
def app_endpoint_poisson_parity_projection_translate (f : ℤ → ℝ) : ℤ → ℝ :=
  fun n => f (n + 1)

/-- Three-point convolution with the even endpoint kernel `K_ρ`. -/
def app_endpoint_poisson_parity_projection_operator (ρ : ℝ) (g : ℤ → ℝ) : ℤ → ℝ :=
  fun n => ρ * g (n - 1) + g n + ρ * g (n + 1)

/-- Evenness for the translated endpoint profile. -/
def app_endpoint_poisson_parity_projection_even (g : ℤ → ℝ) : Prop :=
  ∀ n, g (-n) = g n

/-- Oddness for the translated endpoint profile. -/
def app_endpoint_poisson_parity_projection_odd (g : ℤ → ℝ) : Prop :=
  ∀ n, g (-n) = -g n

/-- Central first difference at the endpoint, standing in for the derivative at `0`. -/
def app_endpoint_poisson_parity_projection_central_slope (g : ℤ → ℝ) : ℝ :=
  g 1 - g (-1)

/-- Concrete parity-projection package for the endpoint Poisson operator after translating by
`π`. -/
def app_endpoint_poisson_parity_projection_statement (ρ : ℝ) (f : ℤ → ℝ) : Prop :=
  let g := app_endpoint_poisson_parity_projection_translate f
  let T := app_endpoint_poisson_parity_projection_operator ρ g
  (app_endpoint_poisson_parity_projection_even g →
      app_endpoint_poisson_parity_projection_even T) ∧
    (app_endpoint_poisson_parity_projection_odd g →
      app_endpoint_poisson_parity_projection_odd T) ∧
    (app_endpoint_poisson_parity_projection_even T →
      app_endpoint_poisson_parity_projection_central_slope T = 0) ∧
    (app_endpoint_poisson_parity_projection_odd T →
      T 0 = 0)

private lemma app_endpoint_poisson_parity_projection_operator_preserves_even
    (ρ : ℝ) {g : ℤ → ℝ} (hg : app_endpoint_poisson_parity_projection_even g) :
    app_endpoint_poisson_parity_projection_even
      (app_endpoint_poisson_parity_projection_operator ρ g) := by
  intro n
  have hleft : g (-n - 1) = g (n + 1) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg (n + 1)
  have hmid : g (-n) = g n := hg n
  have hright : g (-n + 1) = g (n - 1) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg (n - 1)
  calc
    app_endpoint_poisson_parity_projection_operator ρ g (-n)
        = ρ * g (-n - 1) + g (-n) + ρ * g (-n + 1) := by
            rfl
    _ = ρ * g (n + 1) + g n + ρ * g (n - 1) := by
          rw [hleft, hmid, hright]
    _ = ρ * g (n - 1) + g n + ρ * g (n + 1) := by
          ring
    _ = app_endpoint_poisson_parity_projection_operator ρ g n := by
          rfl

private lemma app_endpoint_poisson_parity_projection_operator_preserves_odd
    (ρ : ℝ) {g : ℤ → ℝ} (hg : app_endpoint_poisson_parity_projection_odd g) :
    app_endpoint_poisson_parity_projection_odd
      (app_endpoint_poisson_parity_projection_operator ρ g) := by
  intro n
  have hleft : g (-n - 1) = -g (n + 1) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg (n + 1)
  have hmid : g (-n) = -g n := hg n
  have hright : g (-n + 1) = -g (n - 1) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg (n - 1)
  calc
    app_endpoint_poisson_parity_projection_operator ρ g (-n)
        = ρ * g (-n - 1) + g (-n) + ρ * g (-n + 1) := by
            rfl
    _ = ρ * (-g (n + 1)) + (-g n) + ρ * (-g (n - 1)) := by
          rw [hleft, hmid, hright]
    _ = -(ρ * g (n - 1) + g n + ρ * g (n + 1)) := by
          ring
    _ = -app_endpoint_poisson_parity_projection_operator ρ g n := by
          rfl

private lemma app_endpoint_poisson_parity_projection_even_central_slope_zero
    {g : ℤ → ℝ} (hg : app_endpoint_poisson_parity_projection_even g) :
    app_endpoint_poisson_parity_projection_central_slope g = 0 := by
  have h1 : g (-1) = g 1 := hg 1
  dsimp [app_endpoint_poisson_parity_projection_central_slope]
  linarith

private lemma app_endpoint_poisson_parity_projection_odd_value_zero
    {g : ℤ → ℝ} (hg : app_endpoint_poisson_parity_projection_odd g) :
    g 0 = 0 := by
  have h0 : g 0 = -g 0 := hg 0
  linarith

/-- Paper label: `lem:app-endpoint-poisson-parity-projection`. After translating to the endpoint
chart, convolution with the even kernel `K_ρ` preserves parity; hence an even endpoint profile has
vanishing central slope at `0`, while an odd endpoint profile vanishes at `0`. -/
theorem paper_app_endpoint_poisson_parity_projection (ρ : ℝ) (f : ℤ → ℝ) :
    app_endpoint_poisson_parity_projection_statement ρ f := by
  dsimp [app_endpoint_poisson_parity_projection_statement]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hg
    exact app_endpoint_poisson_parity_projection_operator_preserves_even ρ hg
  · intro hg
    exact app_endpoint_poisson_parity_projection_operator_preserves_odd ρ hg
  · intro hT
    exact app_endpoint_poisson_parity_projection_even_central_slope_zero hT
  · intro hT
    exact app_endpoint_poisson_parity_projection_odd_value_zero hT

end Omega.UnitCirclePhaseArithmetic
