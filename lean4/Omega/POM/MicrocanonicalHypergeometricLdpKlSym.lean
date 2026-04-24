import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldPosteriorCountAndProb

namespace Omega.POM

noncomputable section

/-- Residual-profile involution induced by the mass-conservation relation `1 = β q + (1 - β) r`. -/
def pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile (beta q : ℝ) : ℝ :=
  (1 - beta * q) / (1 - beta)

/-- Scalar KL seed used to package the explicit rate function. -/
def pom_microcanonical_hypergeometric_ldp_kl_sym_kl (x w : ℝ) : ℝ :=
  x * Real.log (x / w)

/-- Hypergeometric sample-profile rate function `J_β`. -/
def pom_microcanonical_hypergeometric_ldp_kl_sym_rate (beta q : ℝ) : ℝ :=
  beta * pom_microcanonical_hypergeometric_ldp_kl_sym_kl q 1 +
    (1 - beta) *
      pom_microcanonical_hypergeometric_ldp_kl_sym_kl
        (pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile beta q) 1

/-- Paper-facing wrapper for the explicit KL form of the sample/residual rate package and its
`β ↔ 1 - β` symmetry under the residual involution. -/
def pomMicrocanonicalHypergeometricLdpKlSymStatement (beta : ℝ) : Prop :=
  ∀ q : ℝ,
    let r := pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile beta q
    pom_microcanonical_hypergeometric_ldp_kl_sym_rate beta q =
        beta * pom_microcanonical_hypergeometric_ldp_kl_sym_kl q 1 +
          (1 - beta) * pom_microcanonical_hypergeometric_ldp_kl_sym_kl r 1 ∧
      pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile (1 - beta) r = q ∧
      pom_microcanonical_hypergeometric_ldp_kl_sym_rate beta q =
        pom_microcanonical_hypergeometric_ldp_kl_sym_rate (1 - beta) r

/-- Paper label: `thm:pom-microcanonical-hypergeometric-ldp-kl-sym`. The finite-composition
hypergeometric rate is the explicit KL sum obtained from the sample and residual profiles, and the
mass-conservation involution `q ↦ r(q)` exchanges the `β` and `1 - β` weights without changing the
rate. -/
theorem paper_pom_microcanonical_hypergeometric_ldp_kl_sym
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    pomMicrocanonicalHypergeometricLdpKlSymStatement beta := by
  have hbeta_ne0 : beta ≠ 0 := ne_of_gt hbeta0
  have hone_beta_ne : 1 - beta ≠ 0 := sub_ne_zero.mpr (ne_of_lt hbeta1).symm
  intro q
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · unfold pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile
    field_simp [hbeta_ne0, hone_beta_ne]
    ring
  · have hresidual :
        pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile
            (1 - beta)
            (pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile beta q) =
          q := by
      unfold pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile
      field_simp [hbeta_ne0, hone_beta_ne]
      ring
    have hresidual_expanded :
        (1 - (1 - beta) * ((1 - beta * q) / (1 - beta))) / (1 - (1 - beta)) = q := by
      unfold pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile at hresidual
      simpa using hresidual
    unfold pom_microcanonical_hypergeometric_ldp_kl_sym_rate
      pom_microcanonical_hypergeometric_ldp_kl_sym_residualProfile
    rw [hresidual_expanded]
    ring

end

end Omega.POM
