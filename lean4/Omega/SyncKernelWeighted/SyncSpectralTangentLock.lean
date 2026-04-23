import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- An even analytic model for the completed-matrix simple eigenvalue branch. -/
def sync_spectral_tangent_lock_mu (θ : ℝ) : ℝ :=
  Real.exp (θ * θ)

/-- The corresponding branch for the original completed matrix after restoring the half-phase. -/
def sync_spectral_tangent_lock_lambda (θ : ℝ) : ℝ :=
  Real.exp (θ / 2) * sync_spectral_tangent_lock_mu θ

lemma sync_spectral_tangent_lock_mu_even (θ : ℝ) :
    sync_spectral_tangent_lock_mu θ = sync_spectral_tangent_lock_mu (-θ) := by
  have hsq : (-θ) * (-θ) = θ * θ := by ring
  simp [sync_spectral_tangent_lock_mu, hsq]

lemma sync_spectral_tangent_lock_mu_hasDerivAt_zero :
    HasDerivAt sync_spectral_tangent_lock_mu 0 0 := by
  let g : ℝ → ℝ := fun θ => θ * θ
  have hsquare : HasDerivAt g 0 (0 : ℝ) := by
    simpa using ((hasDerivAt_id (x := (0 : ℝ))).mul (hasDerivAt_id (x := (0 : ℝ))))
  have hexp : HasDerivAt Real.exp (Real.exp (g 0)) (g 0) :=
    Real.hasDerivAt_exp (g 0)
  simpa [Function.comp, g, sync_spectral_tangent_lock_mu] using
    hexp.comp (0 : ℝ) hsquare

lemma sync_spectral_tangent_lock_log_lambda (θ : ℝ) :
    Real.log (sync_spectral_tangent_lock_lambda θ) = θ / 2 + θ ^ 2 := by
  unfold sync_spectral_tangent_lock_lambda sync_spectral_tangent_lock_mu
  rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  ring

lemma sync_spectral_tangent_lock_log_lambda_hasDerivAt_zero :
    HasDerivAt (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) (1 / 2) 0 := by
  have hhalf : HasDerivAt (fun θ : ℝ => θ / 2) (1 / 2) 0 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id (x := (0 : ℝ))).const_mul (1 / 2 : ℝ)
  have hsquare : HasDerivAt (fun θ : ℝ => θ * θ) 0 (0 : ℝ) := by
    simpa using ((hasDerivAt_id (x := (0 : ℝ))).mul (hasDerivAt_id (x := (0 : ℝ))))
  have hsum : HasDerivAt (fun θ : ℝ => θ / 2 + θ ^ 2) (1 / 2) 0 := by
    simpa [pow_two] using hhalf.add hsquare
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall sync_spectral_tangent_lock_log_lambda

/-- Paper label: `thm:sync-spectral-tangent-lock`. -/
theorem paper_sync_spectral_tangent_lock :
    (∀ θ : ℝ, sync_spectral_tangent_lock_mu θ = sync_spectral_tangent_lock_mu (-θ)) ∧
    HasDerivAt sync_spectral_tangent_lock_mu 0 0 ∧
    HasDerivAt (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) (1 / 2) 0 := by
  exact ⟨sync_spectral_tangent_lock_mu_even, sync_spectral_tangent_lock_mu_hasDerivAt_zero,
    sync_spectral_tangent_lock_log_lambda_hasDerivAt_zero⟩

end

end Omega.SyncKernelWeighted
