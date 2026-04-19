import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- A concrete sequential formulation of the vanishing defect limit. -/
def defectLimitZero (defect : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |defect n| < ε

/-- In this file, the RH-facing purity criterion is the same concrete limit condition. -/
def rhHorizonPurity (defect : ℕ → ℝ) : Prop :=
  defectLimitZero defect

/-- The repulsion radius attached to a radius/defect pair. -/
noncomputable def repulsionRadius (rho defect : ℝ) : ℝ :=
  rho * Real.exp (-defect)

/-- A concrete zero-free certificate records that the repulsion radius stays inside `(0, rho]`. -/
def repulsionRadiusZeroFreeCertificate (rho defect : ℝ) : Prop :=
  0 < repulsionRadius rho defect ∧ repulsionRadius rho defect ≤ rho

/-- A simple sequential notion of convergence to `1`. -/
def radiiTendToOne (rho : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |rho n - 1| < ε

theorem rh_iff_defect_limit_zero (defect : ℕ → ℝ) :
    rhHorizonPurity defect ↔ defectLimitZero defect := by
  rfl

theorem repulsion_radius_zero_free_certificate
    {rho defect : ℝ} (hrho : 0 < rho) (hrho_le_one : rho ≤ 1) (hdefect : 0 ≤ defect) :
    repulsionRadiusZeroFreeCertificate rho defect := by
  refine ⟨?_, ?_⟩
  · have hexp_pos : 0 < Real.exp (-defect) := Real.exp_pos (-defect)
    simpa [repulsionRadius] using mul_pos hrho hexp_pos
  · have hneg : -defect ≤ 0 := by linarith
    have hexp_le_one : Real.exp (-defect) ≤ 1 := by
      have := Real.exp_le_exp.mpr hneg
      simpa using this
    have hrho_nonneg : 0 ≤ rho := le_of_lt hrho
    simpa [repulsionRadius] using mul_le_mul_of_nonneg_left hexp_le_one hrho_nonneg

theorem defect_eq_zero_of_repulsion_eq_radius
    {rho defect : ℝ} (hrho : 0 < rho) (heq : repulsionRadius rho defect = rho) :
    defect = 0 := by
  have hrho_ne : rho ≠ 0 := ne_of_gt hrho
  have hdiv := congrArg (fun x : ℝ => x / rho) heq
  have hexp : Real.exp (-defect) = 1 := by
    simpa [repulsionRadius, hrho_ne] using hdiv
  have hneg : -defect = 0 := by
    calc
      -defect = Real.log (Real.exp (-defect)) := by rw [Real.log_exp]
      _ = Real.log 1 := by rw [hexp]
      _ = 0 := Real.log_one
  linarith

theorem repulsion_radius_tends_to_one_implies_rh
    (defect rho : ℕ → ℝ) (hTend : radiiTendToOne rho) (hrho : ∀ n, 0 < rho n)
    (heq : ∀ n, repulsionRadius (rho n) (defect n) = rho n) :
    rhHorizonPurity defect := by
  have hRepulsionTend : radiiTendToOne (fun n => repulsionRadius (rho n) (defect n)) := by
    simpa [heq] using hTend
  have hzero : ∀ n, defect n = 0 := by
    intro n
    exact defect_eq_zero_of_repulsion_eq_radius (hrho n) (heq n)
  intro ε hε
  refine ⟨0, ?_⟩
  intro n hn
  simpa [hzero n] using hε

/-- Paper-facing concrete package for horizon purity and the repulsion-radius certificate.
    thm:typed-address-biaxial-completion-horizon-purity-repulsion -/
theorem paper_typed_address_biaxial_completion_horizon_purity_repulsion :
    (∀ defect : ℕ → ℝ, rhHorizonPurity defect ↔ defectLimitZero defect) ∧
      (∀ {rho defect : ℝ}, 0 < rho → rho ≤ 1 → 0 ≤ defect →
        repulsionRadiusZeroFreeCertificate rho defect) ∧
      (∀ defect rho : ℕ → ℝ, radiiTendToOne rho →
        (∀ n, 0 < rho n) →
        (∀ n, repulsionRadius (rho n) (defect n) = rho n) →
        rhHorizonPurity defect) := by
  exact ⟨rh_iff_defect_limit_zero,
    fun {rho defect} hrho hrho_le_one hdefect =>
      repulsion_radius_zero_free_certificate hrho hrho_le_one hdefect,
    repulsion_radius_tends_to_one_implies_rh⟩

end Omega.TypedAddressBiaxialCompletion
