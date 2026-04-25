import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.LkAreaLawQform

namespace Omega.POM

noncomputable section

/-- The hyperbolic parameter used in the `K_k` strong Szego decomposition. -/
def pom_kk_strong_szego_bulk_surface_eta (t : ℝ) : ℝ :=
  pom_lk_area_law_qform_eta t

/-- The associated nome `q = exp (-2 eta)`. -/
def pom_kk_strong_szego_bulk_surface_q (t : ℝ) : ℝ :=
  pom_lk_area_law_qform_q t

/-- The normalized symbol integral giving the bulk density. -/
def pom_kk_strong_szego_bulk_surface_symbol_integral (t : ℝ) : ℝ :=
  2 * pom_kk_strong_szego_bulk_surface_eta t

/-- The finite-volume bulk contribution. -/
def pom_kk_strong_szego_bulk_surface_bulk (k : ℕ) (t : ℝ) : ℝ :=
  (k : ℝ) * pom_kk_strong_szego_bulk_surface_symbol_integral t

/-- The surface contribution in q-form normalization. -/
def pom_kk_strong_szego_bulk_surface_surface (t : ℝ) : ℝ :=
  -Real.log (1 + pom_kk_strong_szego_bulk_surface_q t)

/-- The exponentially small finite-size correction. -/
def pom_kk_strong_szego_bulk_surface_remainder (k : ℕ) (t : ℝ) : ℝ :=
  Real.log (1 + pom_kk_strong_szego_bulk_surface_q t ^ (2 * k + 1))

/-- The log-determinant model decomposed into bulk, surface, and finite-size parts. -/
def pom_kk_strong_szego_bulk_surface_log_det_model (k : ℕ) (t : ℝ) : ℝ :=
  pom_kk_strong_szego_bulk_surface_bulk k t +
    pom_kk_strong_szego_bulk_surface_surface t +
      pom_kk_strong_szego_bulk_surface_remainder k t

/-- Concrete strong Szego bulk/surface package for the `K_k` determinant. It reuses the q-form
determinant identity and log split from the `L_k` package and records the symbol integral
normalization as the bulk density `2 * eta(t)`. -/
def pom_kk_strong_szego_bulk_surface_statement (k : ℕ) (t : ℝ) : Prop :=
  pom_lk_area_law_qform_det_identity k t ∧
    pom_lk_area_law_qform_log_split k t ∧
      pom_lk_area_law_qform_remainder_bound k t ∧
        pom_kk_strong_szego_bulk_surface_symbol_integral t =
          2 * pom_kk_strong_szego_bulk_surface_eta t ∧
          pom_kk_strong_szego_bulk_surface_log_det_model k t =
            2 * (k : ℝ) * pom_kk_strong_szego_bulk_surface_eta t -
              Real.log (1 + pom_kk_strong_szego_bulk_surface_q t) +
                Real.log (1 + pom_kk_strong_szego_bulk_surface_q t ^ (2 * k + 1))

lemma pom_kk_strong_szego_bulk_surface_symbol_integral_eq (t : ℝ) :
    pom_kk_strong_szego_bulk_surface_symbol_integral t =
      2 * pom_kk_strong_szego_bulk_surface_eta t := by
  rfl

lemma pom_kk_strong_szego_bulk_surface_log_det_model_eq (k : ℕ) (t : ℝ) :
    pom_kk_strong_szego_bulk_surface_log_det_model k t =
      2 * (k : ℝ) * pom_kk_strong_szego_bulk_surface_eta t -
        Real.log (1 + pom_kk_strong_szego_bulk_surface_q t) +
          Real.log (1 + pom_kk_strong_szego_bulk_surface_q t ^ (2 * k + 1)) := by
  unfold pom_kk_strong_szego_bulk_surface_log_det_model
    pom_kk_strong_szego_bulk_surface_bulk
    pom_kk_strong_szego_bulk_surface_surface
    pom_kk_strong_szego_bulk_surface_remainder
    pom_kk_strong_szego_bulk_surface_symbol_integral
  ring

/-- Paper label: `prop:pom-Kk-strong-szego-bulk-surface`. -/
theorem paper_pom_kk_strong_szego_bulk_surface (k : ℕ) (t : ℝ) (ht : 0 < t) :
    pom_kk_strong_szego_bulk_surface_statement k t := by
  have hqform := paper_pom_lk_area_law_qform k t ht
  exact ⟨hqform.1, hqform.2.1, hqform.2.2,
    pom_kk_strong_szego_bulk_surface_symbol_integral_eq t,
    pom_kk_strong_szego_bulk_surface_log_det_model_eq k t⟩

end

end Omega.POM
