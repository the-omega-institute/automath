import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- The three collision components used for the finite trace-`3` Poisson certificate. -/
def gm_trace3_poisson_collision_energy_component (a i : Fin 3) : ℝ :=
  if a = i then 1 else 0

/-- The finite Gram entry of the component collision operators. -/
def gm_trace3_poisson_collision_energy_gram (a b : Fin 3) : ℝ :=
  ∑ i : Fin 3,
    gm_trace3_poisson_collision_energy_component a i *
      gm_trace3_poisson_collision_energy_component b i

/-- Squared Euclidean norm on the three certified residual coordinates. -/
def gm_trace3_poisson_collision_energy_sqnorm (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, v i ^ 2

/-- Package the three scalar component coefficients into one residual vector. -/
def gm_trace3_poisson_collision_energy_operator (x0 x1 x2 : ℝ) (i : Fin 3) : ℝ :=
  x0 * gm_trace3_poisson_collision_energy_component 0 i +
    x1 * gm_trace3_poisson_collision_energy_component 1 i +
      x2 * gm_trace3_poisson_collision_energy_component 2 i

/-- The squared-norm identity for the three component collision maps. -/
def gm_trace3_poisson_collision_energy_squared_norm_identity : Prop :=
  ∀ x0 x1 x2 : ℝ,
    gm_trace3_poisson_collision_energy_sqnorm
        (gm_trace3_poisson_collision_energy_operator x0 x1 x2) =
      x0 ^ 2 + x1 ^ 2 + x2 ^ 2

/-- The finite PSD certificate obtained from the Gram matrix of the component maps. -/
def gm_trace3_poisson_collision_energy_finite_psd_certificate : Prop :=
  ∀ x0 x1 x2 : ℝ,
    0 ≤
        x0 * x0 * gm_trace3_poisson_collision_energy_gram 0 0 +
          x0 * x1 * gm_trace3_poisson_collision_energy_gram 0 1 +
          x0 * x2 * gm_trace3_poisson_collision_energy_gram 0 2 +
          x1 * x0 * gm_trace3_poisson_collision_energy_gram 1 0 +
          x1 * x1 * gm_trace3_poisson_collision_energy_gram 1 1 +
          x1 * x2 * gm_trace3_poisson_collision_energy_gram 1 2 +
          x2 * x0 * gm_trace3_poisson_collision_energy_gram 2 0 +
          x2 * x1 * gm_trace3_poisson_collision_energy_gram 2 1 +
          x2 * x2 * gm_trace3_poisson_collision_energy_gram 2 2

/-- The component Gram/operator certificate for the Poisson collision residual. -/
def gm_trace3_poisson_collision_energy_statement : Prop :=
  gm_trace3_poisson_collision_energy_squared_norm_identity ∧
    gm_trace3_poisson_collision_energy_finite_psd_certificate

/-- Paper label: `prop:gm-trace3-poisson-collision-energy`. -/
theorem paper_gm_trace3_poisson_collision_energy :
    gm_trace3_poisson_collision_energy_statement := by
  constructor
  · intro x0 x1 x2
    simp [gm_trace3_poisson_collision_energy_sqnorm,
      gm_trace3_poisson_collision_energy_operator,
      gm_trace3_poisson_collision_energy_component, Fin.sum_univ_three]
  · intro x0 x1 x2
    simp [gm_trace3_poisson_collision_energy_gram,
      gm_trace3_poisson_collision_energy_component]
    nlinarith [sq_nonneg x0, sq_nonneg x1, sq_nonneg x2]

end Omega.SyncKernelRealInput
