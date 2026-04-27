import Mathlib.Tactic

namespace Omega.POM

/-- Legendre-Fenchel transform used by the POM LDP wrapper. -/
noncomputable def pom_ldp_uniform_and_wm_exact_spectrum_legendre
    (Lambda : ℝ → ℝ) (alpha : ℝ) : ℝ :=
  sSup (Set.range fun q : ℝ => q * alpha - Lambda q)

/-- Concrete data for the double LDP and exact spectrum theorem.

The fields are the actual pressure, log-MGF, rate, and spectrum functions appearing in the
statement, together with the concrete Gartner--Ellis outputs needed by the paper-facing wrapper. -/
structure pom_ldp_uniform_and_wm_exact_spectrum_data where
  pom_ldp_uniform_and_wm_exact_spectrum_tau : ℝ → ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_logPhi : ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_lambdaUniform : ℝ → ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_lambdaWm : ℝ → ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_rateUniform : ℝ → ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_rateWm : ℝ → ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_fiberSpectrum : ℝ → ℝ
  pom_ldp_uniform_and_wm_exact_spectrum_uniformLogMgfLimit :
    ∀ q : ℝ,
      pom_ldp_uniform_and_wm_exact_spectrum_lambdaUniform q =
        pom_ldp_uniform_and_wm_exact_spectrum_tau q -
          pom_ldp_uniform_and_wm_exact_spectrum_logPhi
  pom_ldp_uniform_and_wm_exact_spectrum_wmLogMgfLimit :
    ∀ q : ℝ,
      pom_ldp_uniform_and_wm_exact_spectrum_lambdaWm q =
        pom_ldp_uniform_and_wm_exact_spectrum_tau (q + 1) - Real.log 2
  pom_ldp_uniform_and_wm_exact_spectrum_uniformGartnerEllis :
    ∀ alpha : ℝ,
      pom_ldp_uniform_and_wm_exact_spectrum_rateUniform alpha =
        pom_ldp_uniform_and_wm_exact_spectrum_legendre
          pom_ldp_uniform_and_wm_exact_spectrum_lambdaUniform alpha
  pom_ldp_uniform_and_wm_exact_spectrum_wmGartnerEllis :
    ∀ alpha : ℝ,
      pom_ldp_uniform_and_wm_exact_spectrum_rateWm alpha =
        pom_ldp_uniform_and_wm_exact_spectrum_legendre
          pom_ldp_uniform_and_wm_exact_spectrum_lambdaWm alpha
  pom_ldp_uniform_and_wm_exact_spectrum_localCountingEquality :
    ∀ alpha : ℝ,
      pom_ldp_uniform_and_wm_exact_spectrum_fiberSpectrum alpha =
        pom_ldp_uniform_and_wm_exact_spectrum_logPhi -
          pom_ldp_uniform_and_wm_exact_spectrum_rateUniform alpha

/-- Uniform-measure LDP conclusion retained by the paper wrapper. -/
def pom_ldp_uniform_and_wm_exact_spectrum_uniform_ldp
    (D : pom_ldp_uniform_and_wm_exact_spectrum_data) : Prop :=
  (∀ q : ℝ,
      D.pom_ldp_uniform_and_wm_exact_spectrum_lambdaUniform q =
        D.pom_ldp_uniform_and_wm_exact_spectrum_tau q -
          D.pom_ldp_uniform_and_wm_exact_spectrum_logPhi) ∧
    ∀ alpha : ℝ,
      D.pom_ldp_uniform_and_wm_exact_spectrum_rateUniform alpha =
        pom_ldp_uniform_and_wm_exact_spectrum_legendre
          D.pom_ldp_uniform_and_wm_exact_spectrum_lambdaUniform alpha

/-- Push-forward `w_m` LDP conclusion retained by the paper wrapper. -/
def pom_ldp_uniform_and_wm_exact_spectrum_wm_ldp
    (D : pom_ldp_uniform_and_wm_exact_spectrum_data) : Prop :=
  (∀ q : ℝ,
      D.pom_ldp_uniform_and_wm_exact_spectrum_lambdaWm q =
        D.pom_ldp_uniform_and_wm_exact_spectrum_tau (q + 1) - Real.log 2) ∧
    ∀ alpha : ℝ,
      D.pom_ldp_uniform_and_wm_exact_spectrum_rateWm alpha =
        pom_ldp_uniform_and_wm_exact_spectrum_legendre
          D.pom_ldp_uniform_and_wm_exact_spectrum_lambdaWm alpha

/-- Exact local multifractal spectrum conclusion. -/
def pom_ldp_uniform_and_wm_exact_spectrum_exact_spectrum
    (D : pom_ldp_uniform_and_wm_exact_spectrum_data) : Prop :=
  ∀ alpha : ℝ,
    D.pom_ldp_uniform_and_wm_exact_spectrum_fiberSpectrum alpha =
      D.pom_ldp_uniform_and_wm_exact_spectrum_logPhi -
        D.pom_ldp_uniform_and_wm_exact_spectrum_rateUniform alpha

/-- Paper-facing statement for `thm:pom-ldp-uniform-and-wm-exact-spectrum`. -/
def pom_ldp_uniform_and_wm_exact_spectrum_statement
    (D : pom_ldp_uniform_and_wm_exact_spectrum_data) : Prop :=
  pom_ldp_uniform_and_wm_exact_spectrum_uniform_ldp D ∧
    pom_ldp_uniform_and_wm_exact_spectrum_wm_ldp D ∧
      pom_ldp_uniform_and_wm_exact_spectrum_exact_spectrum D

/-- Paper label: `thm:pom-ldp-uniform-and-wm-exact-spectrum`. -/
theorem paper_pom_ldp_uniform_and_wm_exact_spectrum
    (D : pom_ldp_uniform_and_wm_exact_spectrum_data) :
    pom_ldp_uniform_and_wm_exact_spectrum_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨D.pom_ldp_uniform_and_wm_exact_spectrum_uniformLogMgfLimit,
      D.pom_ldp_uniform_and_wm_exact_spectrum_uniformGartnerEllis⟩
  · exact ⟨D.pom_ldp_uniform_and_wm_exact_spectrum_wmLogMgfLimit,
      D.pom_ldp_uniform_and_wm_exact_spectrum_wmGartnerEllis⟩
  · exact D.pom_ldp_uniform_and_wm_exact_spectrum_localCountingEquality

end Omega.POM
