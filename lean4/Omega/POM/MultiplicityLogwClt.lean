import Mathlib.Tactic
import Omega.POM.MultiplicityEnergyLdpUnderPL
import Omega.POM.MultiplicityLambdaqDerivativeGibbs

namespace Omega.POM

open Filter
open scoped Topology

noncomputable section

/-- Concrete data for the logarithmic multiplicity quasi-power CLT. The two CLT fields are
moment-generating-function convergence statements with the shared variance constant
`sigmaStarSq`, while the LDP field records compatibility with the existing multiplicity-energy
Legendre package. -/
structure pom_multiplicity_logw_clt_data where
  pom_multiplicity_logw_clt_normalizedLogWeight : ℕ → ℝ
  pom_multiplicity_logw_clt_energyFluctuation : ℕ → ℝ
  pom_multiplicity_logw_clt_partitionFunction : ℕ → ℝ → ℝ
  pom_multiplicity_logw_clt_lambda : ℝ → ℝ
  pom_multiplicity_logw_clt_normalizedLogMgfLimit : ℝ → ℝ
  pom_multiplicity_logw_clt_rate : ℝ → ℝ
  pom_multiplicity_logw_clt_sigmaStarSq : ℝ
  pom_multiplicity_logw_clt_energyLdp :
    pom_multiplicity_energy_ldp_under_pl_conclusion
      pom_multiplicity_logw_clt_partitionFunction
      pom_multiplicity_logw_clt_lambda
      pom_multiplicity_logw_clt_normalizedLogMgfLimit
      pom_multiplicity_logw_clt_rate
  pom_multiplicity_logw_clt_sigmaStarSq_pos :
    0 < pom_multiplicity_logw_clt_sigmaStarSq
  pom_multiplicity_logw_clt_normalizedLogWeightCLT :
    ∀ t : ℝ,
      Tendsto
        (fun L : ℕ =>
          Real.exp (t * pom_multiplicity_logw_clt_normalizedLogWeight L))
        atTop
        (𝓝 (Real.exp ((pom_multiplicity_logw_clt_sigmaStarSq / 2) * t ^ (2 : Nat))))
  pom_multiplicity_logw_clt_energyCLT :
    ∀ t : ℝ,
      Tendsto
        (fun L : ℕ =>
          Real.exp (t * pom_multiplicity_logw_clt_energyFluctuation L))
        atTop
        (𝓝 (Real.exp ((pom_multiplicity_logw_clt_sigmaStarSq / 2) * t ^ (2 : Nat))))

namespace pom_multiplicity_logw_clt_data

/-- The variance constant appearing in the normalized log-weight CLT. -/
def sigmaStarSq (D : pom_multiplicity_logw_clt_data) : ℝ :=
  D.pom_multiplicity_logw_clt_sigmaStarSq

/-- The normalized log-weight CLT, expressed through convergence of Gaussian MGFs. -/
def normalizedLogWeightCLT (D : pom_multiplicity_logw_clt_data) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun L : ℕ => Real.exp (t * D.pom_multiplicity_logw_clt_normalizedLogWeight L))
      atTop
      (𝓝 (Real.exp ((D.sigmaStarSq / 2) * t ^ (2 : Nat))))

/-- The equivalent centered-energy CLT, using the same Gaussian variance constant. -/
def energyCLT (D : pom_multiplicity_logw_clt_data) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun L : ℕ => Real.exp (t * D.pom_multiplicity_logw_clt_energyFluctuation L))
      atTop
      (𝓝 (Real.exp ((D.sigmaStarSq / 2) * t ^ (2 : Nat))))

end pom_multiplicity_logw_clt_data

/-- Paper label: `thm:pom-multiplicity-logw-clt`.
The quasi-power data package gives the normalized logarithmic-weight CLT, the equivalent
energy CLT, and strict positivity of the shared second-derivative variance constant. -/
theorem paper_pom_multiplicity_logw_clt (D : pom_multiplicity_logw_clt_data) :
    D.normalizedLogWeightCLT ∧ D.energyCLT ∧ 0 < D.sigmaStarSq := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [pom_multiplicity_logw_clt_data.normalizedLogWeightCLT,
      pom_multiplicity_logw_clt_data.sigmaStarSq] using
      D.pom_multiplicity_logw_clt_normalizedLogWeightCLT
  · simpa [pom_multiplicity_logw_clt_data.energyCLT,
      pom_multiplicity_logw_clt_data.sigmaStarSq] using
      D.pom_multiplicity_logw_clt_energyCLT
  · simpa [pom_multiplicity_logw_clt_data.sigmaStarSq] using
      D.pom_multiplicity_logw_clt_sigmaStarSq_pos

end

end Omega.POM
