import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MaxentLift

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite dataset for the fiber-uniform lift MLE comparison.  Positivity of fiber
sizes and nonzero model mass on the observed macrostates are part of the data, so the logarithmic
splitting is valid at every sampled microstate. -/
structure pom_fiber_uniform_lift_mle_equivalence_data where
  macroCount : ℕ
  parameterCount : ℕ
  sampleCount : ℕ
  d : Fin macroCount → ℕ
  d_pos : ∀ x, 0 < d x
  q : Fin parameterCount → Fin macroCount → ℝ
  sample : Fin sampleCount → FiberMicrostate d
  q_sample_ne_zero : ∀ θ j, q θ (sample j).1 ≠ 0

/-- Macro-level log likelihood of the observed lifted dataset. -/
noncomputable def pom_fiber_uniform_lift_mle_equivalence_data.macroLogLikelihood
    (D : pom_fiber_uniform_lift_mle_equivalence_data) (θ : Fin D.parameterCount) : ℝ :=
  ∑ j : Fin D.sampleCount, Real.log (D.q θ (D.sample j).1)

/-- Microstate likelihood after the fiber-uniform lift. -/
noncomputable def pom_fiber_uniform_lift_mle_equivalence_data.liftedLogLikelihood
    (D : pom_fiber_uniform_lift_mle_equivalence_data) (θ : Fin D.parameterCount) : ℝ :=
  ∑ j : Fin D.sampleCount, Real.log (fiberUniformLift D.d (D.q θ) (D.sample j))

/-- The dataset-dependent fiber-size correction. -/
noncomputable def pom_fiber_uniform_lift_mle_equivalence_data.fiberLogCorrection
    (D : pom_fiber_uniform_lift_mle_equivalence_data) : ℝ :=
  ∑ j : Fin D.sampleCount, Real.log (D.d (D.sample j).1)

/-- The set of finite-parameter maximizers of a score. -/
noncomputable def pom_fiber_uniform_lift_mle_equivalence_argmaxSet
    {n : ℕ} (score : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun θ => ∀ θ', score θ' ≤ score θ

/-- Dataset likelihood splits into macro likelihood minus a θ-independent fiber correction. -/
def pom_fiber_uniform_lift_mle_equivalence_data.log_likelihood_splits
    (D : pom_fiber_uniform_lift_mle_equivalence_data) : Prop :=
  ∀ θ : Fin D.parameterCount,
    D.liftedLogLikelihood θ = D.macroLogLikelihood θ - D.fiberLogCorrection

/-- The macro and lifted log likelihoods have the same finite argmax set. -/
def pom_fiber_uniform_lift_mle_equivalence_data.argmax_sets_equal
    (D : pom_fiber_uniform_lift_mle_equivalence_data) : Prop :=
  pom_fiber_uniform_lift_mle_equivalence_argmaxSet D.liftedLogLikelihood =
    pom_fiber_uniform_lift_mle_equivalence_argmaxSet D.macroLogLikelihood

/-- Honest log-splitting lemma for the fiber-uniform lift: the requested paper theorem needs the
numerator to be nonzero. -/
theorem pom_fiber_uniform_lift_mle_equivalence_log_split
    {X Θ : Type} [Fintype X] [DecidableEq X] (d : X → Nat) (hd : ∀ x, 0 < d x) (q : Θ → X → ℝ)
    (θ : Θ) (ω : FiberMicrostate d) (hq : q θ ω.1 ≠ 0) :
    Real.log (q θ ω.1 / d ω.1) = Real.log (q θ ω.1) - Real.log (d ω.1) := by
  have hd0 : (d ω.1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (hd ω.1)
  rw [Real.log_div hq hd0]

/-- Paper label: `prop:pom-fiber-uniform-lift-mle-equivalence`. -/
theorem paper_pom_fiber_uniform_lift_mle_equivalence
    (D : pom_fiber_uniform_lift_mle_equivalence_data) :
    D.log_likelihood_splits ∧ D.argmax_sets_equal := by
  have hsplit : D.log_likelihood_splits := by
    intro θ
    unfold pom_fiber_uniform_lift_mle_equivalence_data.liftedLogLikelihood
    unfold pom_fiber_uniform_lift_mle_equivalence_data.macroLogLikelihood
    unfold pom_fiber_uniform_lift_mle_equivalence_data.fiberLogCorrection
    calc
      (∑ j : Fin D.sampleCount, Real.log (fiberUniformLift D.d (D.q θ) (D.sample j))) =
          ∑ j : Fin D.sampleCount,
            (Real.log (D.q θ (D.sample j).1) - Real.log (D.d (D.sample j).1)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [fiberUniformLift] using
              pom_fiber_uniform_lift_mle_equivalence_log_split D.d D.d_pos D.q θ
                (D.sample j) (D.q_sample_ne_zero θ j)
      _ = (∑ j : Fin D.sampleCount, Real.log (D.q θ (D.sample j).1)) -
            ∑ j : Fin D.sampleCount, Real.log (D.d (D.sample j).1) := by
            rw [Finset.sum_sub_distrib]
  refine ⟨hsplit, ?_⟩
  unfold pom_fiber_uniform_lift_mle_equivalence_data.argmax_sets_equal
  apply Finset.ext
  intro θ
  simp [pom_fiber_uniform_lift_mle_equivalence_argmaxSet]
  constructor
  · intro h θ'
    have hθ' := hsplit θ'
    have hθ := hsplit θ
    have hle := h θ'
    linarith
  · intro h θ'
    have hθ' := hsplit θ'
    have hθ := hsplit θ
    have hle := h θ'
    linarith

end Omega.POM
