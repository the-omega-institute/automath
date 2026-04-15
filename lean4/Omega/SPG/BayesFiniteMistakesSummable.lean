import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Omega.SPG.ScanProjectionBayesOptimality

open Filter

namespace Omega.SPG

open ScanProjectionBayesOptimality

noncomputable section

/-- The mismatch event between the target set and the Bayes-optimal decision for an observable. -/
def bayesMismatchEvent {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) : Set α :=
  symmDiff P (observableEvent obs (optimalObservableSet μ obs P))

private theorem bayesMismatchEvent_measure_eq_scanError
    {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    μ.toMeasure (bayesMismatchEvent μ obs P) = scanError μ obs P := by
  rw [PMF.toMeasure_apply_fintype]
  simpa [bayesMismatchEvent, observableApproxError] using
    (observableApproxError_optimal_eq_scanError μ obs P)

private theorem not_mem_bayesMismatchEvent_iff
    {α β : Type*} [Fintype α] (μ : PMF α) (obs : α → β) (P : Set α) (x : α) :
    x ∉ bayesMismatchEvent μ obs P ↔
      (x ∈ observableEvent obs (optimalObservableSet μ obs P) ↔ x ∈ P) := by
  by_cases hP : x ∈ P <;> by_cases hQ : x ∈ observableEvent obs (optimalObservableSet μ obs P)
  · simp [bayesMismatchEvent, Set.mem_symmDiff, hP, hQ]
  · simp [bayesMismatchEvent, Set.mem_symmDiff, hP, hQ]
  · simp [bayesMismatchEvent, Set.mem_symmDiff, hP, hQ]
  · simp [bayesMismatchEvent, Set.mem_symmDiff, hP, hQ]

set_option maxHeartbeats 400000 in
/-- Publication-facing Borel-Cantelli wrapper for Bayes-optimal observable decisions.
    thm:spg-bayes-finite-mistakes-summable -/
theorem paper_spg_bayes_finite_mistakes_summable
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (P : Set α) {β : ℕ → Type*} [∀ m, Fintype (β m)]
    (obs : ∀ m, α → β m)
    (hsum : (∑' m, scanError μ (obs m) P) ≠ ⊤) :
    ∀ᵐ x ∂μ.toMeasure,
      {m | x ∈ bayesMismatchEvent μ (obs m) P}.Finite ∧
      ∀ᶠ m in atTop,
        (x ∈ observableEvent (obs m) (optimalObservableSet μ (obs m) P) ↔ x ∈ P) := by
  have hmeasEq :
      (fun m => μ.toMeasure (bayesMismatchEvent μ (obs m) P)) =
        fun m => scanError μ (obs m) P := by
    funext m
    exact bayesMismatchEvent_measure_eq_scanError μ (obs m) P
  have hmass :
      (∑' m, μ.toMeasure (bayesMismatchEvent μ (obs m) P)) ≠ ⊤ := by
    simpa [hmeasEq] using hsum
  have hfinite :
      ∀ᵐ x ∂μ.toMeasure, {m | x ∈ bayesMismatchEvent μ (obs m) P}.Finite :=
    MeasureTheory.ae_finite_setOf_mem hmass
  have hevent :
      ∀ᵐ x ∂μ.toMeasure, ∀ᶠ m in atTop, x ∉ bayesMismatchEvent μ (obs m) P :=
    MeasureTheory.ae_eventually_notMem hmass
  filter_upwards [hfinite, hevent] with x hxfinite hxevent
  refine ⟨hxfinite, hxevent.mono ?_⟩
  intro m hxm
  exact (not_mem_bayesMismatchEvent_iff μ (obs m) P x).mp hxm

end

end Omega.SPG
