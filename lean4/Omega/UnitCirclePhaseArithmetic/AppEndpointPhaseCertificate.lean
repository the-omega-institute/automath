import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppEndpointBlaschkeRadialAbsorption
import Omega.UnitCirclePhaseArithmetic.AppEndpointPhaseCurrentOffcritical
import Omega.UnitCirclePhaseArithmetic.AppRhIffDiskZeroFree

namespace Omega.UnitCirclePhaseArithmetic

open AppRhIffDiskZeroFreeData

noncomputable section

/-- Paper-facing endpoint phase certificate: vanishing endpoint current forces the finite
Blaschke root list to be empty, so any separate empty-root disk-zero-free certificate upgrades to
RH; the off-critical transport inequality gives the auditable upper bound on the total offset. -/
def app_endpoint_phase_certificate_statement (roots : List ℂ) (deltas : List ℝ)
    (D : AppRhIffDiskZeroFreeData) : Prop :=
  ((∀ a ∈ roots, ‖a‖ < 1) →
      endpointBlaschkeRadialAbsorption roots = 0 →
      (roots = [] → D.diskZeroFree) →
      D.riemannHypothesis) ∧
    (List.Forall₂ TransportedOffcriticalZero roots deltas →
      deltas.sum ≤ endpointBlaschkeRadialAbsorption roots)

private lemma app_endpoint_phase_certificate_endpoint_term_pos {a : ℂ} (ha : ‖a‖ < 1) :
    0 < endpointPoissonMinusOne a := by
  unfold endpointPoissonMinusOne
  have hnum : 0 < 1 - ‖a‖ ^ 2 := by
    have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
    nlinarith
  have hneq : 1 + a ≠ 0 := by
    intro h
    have h' : a + 1 = 0 := by simp [add_comm] at h ⊢; exact h
    have haeq : a = (-1 : ℂ) := eq_neg_of_add_eq_zero_left h'
    have : ‖a‖ = 1 := by simp [haeq]
    linarith
  have hden : 0 < ‖1 + a‖ ^ 2 := by
    have hnorm_pos : 0 < ‖1 + a‖ := norm_pos_iff.mpr hneq
    positivity
  exact div_pos hnum hden

private lemma app_endpoint_phase_certificate_empty_of_zero {roots : List ℂ}
    (hroots : ∀ a ∈ roots, ‖a‖ < 1) (hzero : endpointBlaschkeRadialAbsorption roots = 0) :
    roots = [] := by
  induction roots with
  | nil =>
      rfl
  | cons a roots ih =>
      have ha : ‖a‖ < 1 := hroots a (by simp)
      have htail : ∀ b ∈ roots, ‖b‖ < 1 := by
        intro b hb
        exact hroots b (by simp [hb])
      have htail_nonneg : 0 ≤ endpointBlaschkeRadialAbsorption roots := by
        exact (paper_app_endpoint_blaschke_radial_absorption roots).2.2.2 htail
      have hhead_pos : 0 < endpointPoissonMinusOne a :=
        app_endpoint_phase_certificate_endpoint_term_pos ha
      have hsum_pos : 0 < endpointBlaschkeRadialAbsorption (a :: roots) := by
        simpa [endpointBlaschkeRadialAbsorption] using add_pos_of_pos_of_nonneg hhead_pos htail_nonneg
      exact False.elim ((ne_of_gt hsum_pos) hzero)

/-- Paper label: `cor:app-endpoint-phase-certificate`. Zero endpoint current removes the finite
Blaschke root list, so any disk-zero-free certificate for the empty list returns RH via the
existing disk-zero-free equivalence; the quantitative upper bound is the already formalized
off-critical endpoint-current estimate. -/
theorem paper_app_endpoint_phase_certificate (roots : List ℂ) (deltas : List ℝ)
    (D : AppRhIffDiskZeroFreeData) : app_endpoint_phase_certificate_statement roots deltas D := by
  refine ⟨?_, ?_⟩
  · intro hroots hzero hempty
    have hnil : roots = [] := app_endpoint_phase_certificate_empty_of_zero hroots hzero
    have hDisk : D.diskZeroFree := hempty hnil
    exact (paper_app_rh_iff_disk_zero_free D).2 hDisk
  · intro htransport
    exact (paper_app_endpoint_phase_current_offcritical roots deltas htransport).2

end

end Omega.UnitCirclePhaseArithmetic
