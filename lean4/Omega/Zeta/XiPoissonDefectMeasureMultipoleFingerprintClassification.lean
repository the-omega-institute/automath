import Mathlib.Tactic
import Omega.Zeta.XiPoissonFirstNonvanishingMomentTvKlSharp
import Omega.Zeta.XiPoissonKLRateImpliesMomentCancellation

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the normalized Poisson defect-measure multipole fingerprint. -/
structure xi_poisson_defect_measure_multipole_fingerprint_classification_data where
  xi_poisson_defect_measure_multipole_fingerprint_classification_tvKlData :
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data
  xi_poisson_defect_measure_multipole_fingerprint_classification_cancellationData :
    xi_poisson_kl_rate_implies_moment_cancellation_data

namespace xi_poisson_defect_measure_multipole_fingerprint_classification_data

/-- The TV decay order is the TV part of the first-nonvanishing-moment theorem. -/
def tv_decay_order
    (D : xi_poisson_defect_measure_multipole_fingerprint_classification_data) : Prop :=
  let T := D.xi_poisson_defect_measure_multipole_fingerprint_classification_tvKlData
  T.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tvLimit =
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_tv_closed_constant T

/-- The KL decay order is the KL part of the first-nonvanishing-moment theorem. -/
def kl_decay_order
    (D : xi_poisson_defect_measure_multipole_fingerprint_classification_data) : Prop :=
  let T := D.xi_poisson_defect_measure_multipole_fingerprint_classification_tvKlData
  T.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_klLimit =
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant T

/-- Faster-than-all-multipoles KL decay forces the corresponding moment cancellation. -/
def kl_little_o_implies_moment_cancellation
    (D : xi_poisson_defect_measure_multipole_fingerprint_classification_data) : Prop :=
  xi_poisson_kl_rate_implies_moment_cancellation_data.xi_poisson_kl_rate_implies_moment_cancellation_statement
    D.xi_poisson_defect_measure_multipole_fingerprint_classification_cancellationData

end xi_poisson_defect_measure_multipole_fingerprint_classification_data

/-- Paper label: `thm:xi-poisson-defect-measure-multipole-fingerprint-classification`. -/
theorem paper_xi_poisson_defect_measure_multipole_fingerprint_classification
    (D : xi_poisson_defect_measure_multipole_fingerprint_classification_data) :
    D.tv_decay_order ∧ D.kl_decay_order ∧ D.kl_little_o_implies_moment_cancellation := by
  rcases
    paper_xi_poisson_first_nonvanishing_moment_tv_kl_sharp
      D.xi_poisson_defect_measure_multipole_fingerprint_classification_tvKlData with
    ⟨htv, hkl⟩
  exact
    ⟨by
      simpa [
        xi_poisson_defect_measure_multipole_fingerprint_classification_data.tv_decay_order
      ] using htv, by
      simpa [
        xi_poisson_defect_measure_multipole_fingerprint_classification_data.kl_decay_order
        ] using hkl,
      by
        simpa [
          xi_poisson_defect_measure_multipole_fingerprint_classification_data.kl_little_o_implies_moment_cancellation
        ] using
          paper_xi_poisson_kl_rate_implies_moment_cancellation
            D.xi_poisson_defect_measure_multipole_fingerprint_classification_cancellationData⟩

end

end Omega.Zeta
