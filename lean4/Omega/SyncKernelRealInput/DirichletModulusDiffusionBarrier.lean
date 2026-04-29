import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40NearCoboundarySVP

namespace Omega.SyncKernelRealInput

/-- Concrete one-dimensional specialization of the near-coboundary quadratic-decay package. The
chosen direction packages a single Dirichlet twist, its variance density, the resulting logarithmic
spectral ratio, the exponentiated spectral ratio, and the associated diffusive decay length. -/
structure dirichlet_modulus_diffusion_barrier_data where
  nearCoboundaryData : real_input_40_near_coboundary_svp_data
  modulus : ℝ
  theta : real_input_40_near_coboundary_svp_angle_vector
  sigmaFsq : ℝ
  logSpectralRatio : ℝ
  spectralRatio : ℝ
  decayLength : ℝ
  modulus_pos : 0 < modulus
  logSpectralRatio_eq :
    logSpectralRatio = nearCoboundaryData.real_input_40_near_coboundary_svp_logRatio theta
  quadraticForm_eq :
    real_input_40_near_coboundary_svp_quadratic_form_from_matrix
        nearCoboundaryData.real_input_40_near_coboundary_svp_hessian theta =
      sigmaFsq * (2 * Real.pi / modulus) ^ 2
  spectralRatio_eq : spectralRatio = Real.exp logSpectralRatio
  decayLength_eq : decayLength = modulus ^ 2 / (2 * Real.pi ^ 2 * sigmaFsq)

/-- The packaged Dirichlet modulus corollary: the logarithmic spectral ratio has the explicit
`2π²σ_F² / m²` shape, exponentiating gives the spectral ratio, and the same constants determine
the diffusive decay length. -/
def dirichlet_modulus_diffusion_barrier_statement
    (D : dirichlet_modulus_diffusion_barrier_data) : Prop :=
  D.logSpectralRatio = -(2 * Real.pi ^ 2 * D.sigmaFsq) / D.modulus ^ 2 ∧
    D.spectralRatio = Real.exp (-(2 * Real.pi ^ 2 * D.sigmaFsq) / D.modulus ^ 2) ∧
    D.decayLength = D.modulus ^ 2 / (2 * Real.pi ^ 2 * D.sigmaFsq)

/-- Rewriting the quadratic term along `t_m = 2π / m` produces the displayed
`2π² σ_F² / m²` coefficient. -/
lemma dirichlet_modulus_diffusion_barrier_quadratic_rewrite
    (sigmaFsq modulus : ℝ) (hmodulus : 0 < modulus) :
    -((1 : ℝ) / 2) * (sigmaFsq * (2 * Real.pi / modulus) ^ 2) =
      -(2 * Real.pi ^ 2 * sigmaFsq) / modulus ^ 2 := by
  have hmodulus_ne : modulus ≠ 0 := by positivity
  field_simp [hmodulus_ne]

open real_input_40_near_coboundary_svp_data

/-- Paper label: `cor:dirichlet-modulus-diffusion-barrier`. The general near-coboundary
quadratic-decay package specializes to a one-dimensional Dirichlet twist with an explicit
`m²`-diffusion barrier. -/
theorem paper_dirichlet_modulus_diffusion_barrier
    (D : dirichlet_modulus_diffusion_barrier_data) :
    dirichlet_modulus_diffusion_barrier_statement D := by
  have hquad :=
    (paper_real_input_40_near_coboundary_svp D.nearCoboundaryData).1
  have hlog : D.logSpectralRatio = -(2 * Real.pi ^ 2 * D.sigmaFsq) / D.modulus ^ 2 := by
    calc
      D.logSpectralRatio =
          D.nearCoboundaryData.real_input_40_near_coboundary_svp_logRatio D.theta :=
        D.logSpectralRatio_eq
      _ =
          -((1 : ℝ) / 2) *
            real_input_40_near_coboundary_svp_quadratic_form_from_matrix
              D.nearCoboundaryData.real_input_40_near_coboundary_svp_hessian D.theta :=
        hquad D.theta
      _ = -((1 : ℝ) / 2) * (D.sigmaFsq * (2 * Real.pi / D.modulus) ^ 2) := by
        rw [D.quadraticForm_eq]
      _ = -(2 * Real.pi ^ 2 * D.sigmaFsq) / D.modulus ^ 2 :=
        dirichlet_modulus_diffusion_barrier_quadratic_rewrite D.sigmaFsq D.modulus D.modulus_pos
  refine ⟨hlog, ?_, D.decayLength_eq⟩
  rw [D.spectralRatio_eq, hlog]

end Omega.SyncKernelRealInput
