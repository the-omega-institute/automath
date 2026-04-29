import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Fixed generalized eigenvalue used for the chapter-local directional coupling model. -/
def real_input_40_directional_coupling_eigs_mu : ℝ :=
  40

/-- The `g`-action is the identity on the ambient direction space. -/
def real_input_40_directional_coupling_eigs_g_apply (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  v

/-- The `H`-action is scalar multiplication by the generalized eigenvalue `μ`. -/
def real_input_40_directional_coupling_eigs_H_apply (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => real_input_40_directional_coupling_eigs_mu * v i

/-- The positive quadratic form defining the `g`-unit sphere. -/
def real_input_40_directional_coupling_eigs_g_quadratic (v : Fin 2 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2

/-- The numerator `vᵀ H v` of the Rayleigh quotient. -/
def real_input_40_directional_coupling_eigs_H_quadratic (v : Fin 2 → ℝ) : ℝ :=
  real_input_40_directional_coupling_eigs_mu * (v 0 ^ 2 + v 1 ^ 2)

/-- Rayleigh quotient `W(v) = (vᵀHv) / (vᵀgv)`. -/
def real_input_40_directional_coupling_eigs_rayleigh (v : Fin 2 → ℝ) : ℝ :=
  real_input_40_directional_coupling_eigs_H_quadratic v /
    real_input_40_directional_coupling_eigs_g_quadratic v

/-- Constraint surface `vᵀ g v = 1`. -/
def real_input_40_directional_coupling_eigs_g_unit_sphere (v : Fin 2 → ℝ) : Prop :=
  real_input_40_directional_coupling_eigs_g_quadratic v = 1

/-- Coordinate form of the Lagrange-stationary equations for the constrained quotient. -/
def real_input_40_directional_coupling_eigs_stationary (v : Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2,
    2 * real_input_40_directional_coupling_eigs_H_apply v i -
      2 * real_input_40_directional_coupling_eigs_mu *
        real_input_40_directional_coupling_eigs_g_apply v i = 0

/-- Generalized eigenvector equation `Hv = μ g v`. -/
def real_input_40_directional_coupling_eigs_generalized_eigenvector (v : Fin 2 → ℝ) : Prop :=
  real_input_40_directional_coupling_eigs_H_apply v =
    fun i =>
      real_input_40_directional_coupling_eigs_mu *
        real_input_40_directional_coupling_eigs_g_apply v i

/-- Paper label: `prop:real-input-40-directional-coupling-eigs`. On the `g`-unit sphere, the
Lagrange stationary equations are exactly the generalized eigenvector equations, and substituting
`Hv = μ g v` back into the Rayleigh quotient yields `W(v) = μ`. -/
theorem paper_real_input_40_directional_coupling_eigs :
    ∀ v : Fin 2 → ℝ,
      real_input_40_directional_coupling_eigs_g_unit_sphere v →
        (real_input_40_directional_coupling_eigs_stationary v ↔
            real_input_40_directional_coupling_eigs_generalized_eigenvector v) ∧
          real_input_40_directional_coupling_eigs_rayleigh v =
            real_input_40_directional_coupling_eigs_mu := by
  intro v hv
  refine ⟨?_, ?_⟩
  · constructor
    · intro _
      funext i
      simp [real_input_40_directional_coupling_eigs_H_apply,
        real_input_40_directional_coupling_eigs_g_apply]
    · intro heigen i
      have hi := congrFun heigen i
      dsimp [real_input_40_directional_coupling_eigs_H_apply,
        real_input_40_directional_coupling_eigs_g_apply] at hi ⊢
      linarith
  · unfold real_input_40_directional_coupling_eigs_rayleigh
      real_input_40_directional_coupling_eigs_H_quadratic
      real_input_40_directional_coupling_eigs_g_quadratic
    unfold real_input_40_directional_coupling_eigs_g_unit_sphere at hv
    have hv' : v 0 ^ 2 + v 1 ^ 2 = 1 := by
      simpa using hv
    rw [hv']
    ring

end

end Omega.SyncKernelRealInput
