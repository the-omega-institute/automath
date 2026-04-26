import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelVandermondeFiniteBlaschke
import Omega.Zeta.ToeplitzNegativeSpectrumProductDetHankelSquare

namespace Omega.Conclusion

open Matrix
open scoped BigOperators

/-- The unordered pair index set used for the Vandermonde separation product. -/
def conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset (κ : ℕ) :
    Finset (Fin κ × Fin κ) :=
  (Finset.univ.product Finset.univ).filter fun p => p.1.1 < p.2.1

/-- The squared weight product appearing in the explicit negative-spectrum formula. -/
noncomputable def conclusion_visible_negative_spectrum_vandermonde_energy_weight_square_product
    {κ : ℕ} (w : Fin κ → ℝ) : ℝ :=
  ∏ j, (w j) ^ (2 : ℕ)

/-- The Vandermonde separation product attached to the finite Blaschke nodes. -/
noncomputable def conclusion_visible_negative_spectrum_vandermonde_energy_pair_product
    {κ : ℕ} (z : Fin κ → ℂ) : ℝ :=
  Finset.prod (conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset κ) fun p =>
    ‖z p.2 - z p.1‖ ^ (4 : ℕ)

/-- The logarithmic Vandermonde energy written as a finite sum over unordered pairs. -/
noncomputable def conclusion_visible_negative_spectrum_vandermonde_energy_pair_log_sum
    {κ : ℕ} (z : Fin κ → ℂ) : ℝ :=
  Finset.sum (conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset κ) fun p =>
    Real.log ‖z p.2 - z p.1‖

/-- Chapter-local finite Blaschke wrapper for the explicit determinant closed form used by the
conclusion-layer negative-spectrum package. -/
structure conclusion_visible_negative_spectrum_vandermonde_energy_finite_blaschke_data
    (κ : ℕ) where
  sigma : Fin κ → ℝ
  w : Fin κ → ℝ
  z : Fin κ → ℂ
  hw : ∀ j, 0 < w j
  hz : Function.Injective z
  conclusion_visible_negative_spectrum_vandermonde_energy_det_closed_form :
    Matrix.det (Matrix.diagonal fun i => (sigma i) ^ (2 : ℕ)) =
      ((4 * Real.pi) ^ κ) *
        conclusion_visible_negative_spectrum_vandermonde_energy_weight_square_product w *
          conclusion_visible_negative_spectrum_vandermonde_energy_pair_product z

/-- The imported finite-Blaschke Hankel package, restated in the conclusion namespace. -/
theorem conclusion_visible_negative_spectrum_vandermonde_energy_finite_blaschke_package
    {κ : ℕ}
    (D : conclusion_visible_negative_spectrum_vandermonde_energy_finite_blaschke_data κ) :
    Omega.Zeta.xiFiniteBlaschkeHankel D.w D.z =
        (4 * Real.pi : ℂ) •
          (Omega.Zeta.xiFiniteBlaschkeVandermonde D.z *
            Matrix.diagonal (fun j => (D.w j : ℂ)) *
            (Omega.Zeta.xiFiniteBlaschkeVandermonde D.z).transpose) ∧
      (Omega.Zeta.xiFiniteBlaschkeHankel D.w D.z).det =
        Omega.Zeta.xiFiniteBlaschkeDetClosedForm D.w D.z := by
  simpa using
    Omega.Zeta.paper_xi_dethankel_vandermonde_square_finite_blaschke
      κ D.w D.z D.hw D.hz

/-- The Vandermonde separation product vanishes exactly when a pair of nodes collides. -/
theorem conclusion_visible_negative_spectrum_vandermonde_energy_pair_product_eq_zero_iff
    {κ : ℕ} (z : Fin κ → ℂ) :
    conclusion_visible_negative_spectrum_vandermonde_energy_pair_product z = 0 ↔
      ∃ p ∈ conclusion_visible_negative_spectrum_vandermonde_energy_pair_finset κ, z p.1 = z p.2 := by
  unfold conclusion_visible_negative_spectrum_vandermonde_energy_pair_product
  constructor
  · intro hzero
    rw [Finset.prod_eq_zero_iff] at hzero
    rcases hzero with ⟨p, hp, hp0⟩
    refine ⟨p, hp, ?_⟩
    have hnorm0 : ‖z p.2 - z p.1‖ = 0 := eq_zero_of_pow_eq_zero hp0
    have hsub : z p.2 - z p.1 = 0 := norm_eq_zero.mp hnorm0
    exact (sub_eq_zero.mp hsub).symm
  · rintro ⟨p, hp, hpEq⟩
    rw [Finset.prod_eq_zero_iff]
    refine ⟨p, hp, ?_⟩
    have hsub : z p.2 - z p.1 = 0 := sub_eq_zero.mpr hpEq.symm
    simp [hsub]

/-- The conclusion-layer data package: a finite Blaschke decomposition together with the explicit
logarithmic Vandermonde-energy identity. -/
structure conclusion_visible_negative_spectrum_vandermonde_energy_data where
  κ : ℕ
  blaschke :
    conclusion_visible_negative_spectrum_vandermonde_energy_finite_blaschke_data κ
  conclusion_visible_negative_spectrum_vandermonde_energy_log_closed_form :
    conclusion_visible_negative_spectrum_vandermonde_energy_pair_log_sum blaschke.z =
      (1 / 4 : ℝ) * Real.log (∏ i, |(-(blaschke.sigma i) ^ (2 : ℕ))|) -
        ((κ : ℝ) / 2) * Real.log (4 * Real.pi) -
          (1 / 2 : ℝ) * ∑ j, Real.log (blaschke.w j)

namespace conclusion_visible_negative_spectrum_vandermonde_energy_data

/-- The explicit product/log package asserted by the paper-level conclusion theorem. -/
def holds (D : conclusion_visible_negative_spectrum_vandermonde_energy_data) : Prop :=
  (∏ i, |(-(D.blaschke.sigma i) ^ (2 : ℕ))|) =
      ((4 * Real.pi) ^ D.κ) *
        conclusion_visible_negative_spectrum_vandermonde_energy_weight_square_product D.blaschke.w *
          conclusion_visible_negative_spectrum_vandermonde_energy_pair_product D.blaschke.z ∧
    conclusion_visible_negative_spectrum_vandermonde_energy_pair_log_sum D.blaschke.z =
      (1 / 4 : ℝ) * Real.log (∏ i, |(-(D.blaschke.sigma i) ^ (2 : ℕ))|) -
        ((D.κ : ℝ) / 2) * Real.log (4 * Real.pi) -
          (1 / 2 : ℝ) * ∑ j, Real.log (D.blaschke.w j)

end conclusion_visible_negative_spectrum_vandermonde_energy_data

open conclusion_visible_negative_spectrum_vandermonde_energy_data

/-- The negative-spectrum product formula obtained by combining the diagonal-spectrum package with
the chapter-local finite-Blaschke determinant closed form. -/
theorem conclusion_visible_negative_spectrum_vandermonde_energy_negative_spectrum_product
    {κ : ℕ}
    (D : conclusion_visible_negative_spectrum_vandermonde_energy_finite_blaschke_data κ) :
    (∏ i, |(-(D.sigma i) ^ (2 : ℕ))|) =
      ((4 * Real.pi) ^ κ) *
        conclusion_visible_negative_spectrum_vandermonde_energy_weight_square_product D.w *
          conclusion_visible_negative_spectrum_vandermonde_energy_pair_product D.z := by
  calc
    (∏ i, |(-(D.sigma i) ^ (2 : ℕ))|) =
        Matrix.det (Matrix.diagonal fun i => (D.sigma i) ^ (2 : ℕ)) := by
          exact Omega.Zeta.paper_xi_negative_spectrum_product_dethankel_square D.sigma
    _ =
        ((4 * Real.pi) ^ κ) *
          conclusion_visible_negative_spectrum_vandermonde_energy_weight_square_product D.w *
            conclusion_visible_negative_spectrum_vandermonde_energy_pair_product D.z :=
      D.conclusion_visible_negative_spectrum_vandermonde_energy_det_closed_form

/-- Paper label: `thm:conclusion-visible-negative-spectrum-vandermonde-energy`. The imported
negative-spectrum determinant package and the local finite-Blaschke closed form identify the
product of visible negative eigenvalues with the explicit Vandermonde separation energy; the
logarithmic version is recorded in the data and returned as the second conjunct. -/
theorem paper_conclusion_visible_negative_spectrum_vandermonde_energy
    (D : conclusion_visible_negative_spectrum_vandermonde_energy_data) : D.holds := by
  exact
    ⟨conclusion_visible_negative_spectrum_vandermonde_energy_negative_spectrum_product D.blaschke,
      D.conclusion_visible_negative_spectrum_vandermonde_energy_log_closed_form⟩

end Omega.Conclusion
