import Omega.SPG.ScanErrorDiscrete

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Omega.SPG.ScanProjectionBayesOptimality

noncomputable section

/-- Error mass of approximating `P` by an observable event for `obs`. -/
def observableApproxError {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β) : ENNReal :=
  setMass μ (symmDiff P (observableEvent obs A))

/-- Threshold rule: accept an observation cell exactly when its false-negative mass
    is no larger than its false-positive mass. -/
def optimalObservableSet {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) : Set β :=
  {b | cellComplMass μ obs P b ≤ cellEventMass μ obs P b}

/-- Prefix specialization of `observableApproxError`. -/
def prefixObservableApproxError
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) (A : Set (Word m)) : ENNReal :=
  observableApproxError μ (prefixObservation h) P A

/-- Prefix specialization of the threshold rule. -/
def optimalPrefixDecision
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) : Set (Word m) :=
  optimalObservableSet μ (prefixObservation h) P

theorem cellEventMass_symmDiff_observableEvent_of_mem
    {α β : Type*} [Fintype α] (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β)
    {b : β} (hb : b ∈ A) :
    cellEventMass μ obs (symmDiff P (observableEvent obs A)) b =
      cellComplMass μ obs P b := by
  unfold cellEventMass cellComplMass setMass observableEvent observableCell symmDiff
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : obs x = b
  · by_cases hp : x ∈ P <;> simp [Set.indicator, hx, hp, hb]
  · simp [Set.indicator, hx]

theorem cellEventMass_symmDiff_observableEvent_of_not_mem
    {α β : Type*} [Fintype α] (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β)
    {b : β} (hb : b ∉ A) :
    cellEventMass μ obs (symmDiff P (observableEvent obs A)) b =
      cellEventMass μ obs P b := by
  unfold cellEventMass setMass observableEvent observableCell symmDiff
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : obs x = b
  · by_cases hp : x ∈ P <;> simp [Set.indicator, hx, hp, hb]
  · simp [Set.indicator, hx]

/-- Exact observable-event error decomposition: each observation cell contributes either the
    false-negative mass or the false-positive mass, depending on whether the cell is accepted. -/
theorem observableApproxError_eq_sum_if {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β) :
    observableApproxError μ obs P A =
      ∑ b, if b ∈ A then cellComplMass μ obs P b else cellEventMass μ obs P b := by
  calc
    observableApproxError μ obs P A = setMass μ (symmDiff P (observableEvent obs A)) := rfl
    _ = ∑ b, cellEventMass μ obs (symmDiff P (observableEvent obs A)) b := by
      symm
      exact cellEventMass_sum_eq_setMass μ obs (symmDiff P (observableEvent obs A))
    _ = ∑ b, if b ∈ A then cellComplMass μ obs P b else cellEventMass μ obs P b := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hb : b ∈ A
      · simp [hb, cellEventMass_symmDiff_observableEvent_of_mem μ obs P A hb]
      · simp [hb, cellEventMass_symmDiff_observableEvent_of_not_mem μ obs P A hb]

/-- Any observable-event classifier incurs at least the cellwise Bayes error. -/
theorem scanError_le_observableApproxError {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β) :
    scanError μ obs P ≤ observableApproxError μ obs P A := by
  simpa [observableApproxError] using
    scanError_le_setMass_symmDiff_observableEvent μ obs P A

/-- The threshold rule attains the scan error exactly. -/
theorem observableApproxError_optimal_eq_scanError {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    observableApproxError μ obs P (optimalObservableSet μ obs P) = scanError μ obs P := by
  rw [observableApproxError_eq_sum_if]
  unfold optimalObservableSet scanError
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : cellComplMass μ obs P b ≤ cellEventMass μ obs P b
  · simp [hb]
  · have hb' : cellEventMass μ obs P b ≤ cellComplMass μ obs P b := le_of_not_ge hb
    simp [hb, min_eq_left hb']

/-- Paper-facing seeds for `prop:bayes-optimality`.
    Every prefix-measurable classifier has error at least the scan error, and the threshold
    classifier attains equality. -/
theorem paper_scan_projection_address_bayes_optimality_seeds
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (∀ A : Set (Word m), prefixScanError μ h P ≤ prefixObservableApproxError μ h P A) ∧
    prefixObservableApproxError μ h P (optimalPrefixDecision μ h P) =
      prefixScanError μ h P := by
  constructor
  · intro A
    simpa [prefixScanError, prefixObservableApproxError] using
      (scanError_le_observableApproxError μ (prefixObservation h) P A)
  · simpa [prefixScanError, prefixObservableApproxError, optimalPrefixDecision] using
      (observableApproxError_optimal_eq_scanError μ (prefixObservation h) P)

/-- Packaged form of the `prop:bayes-optimality` seeds. -/
theorem paper_scan_projection_address_bayes_optimality_package
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (∀ A : Set (Word m), prefixScanError μ h P ≤ prefixObservableApproxError μ h P A) ∧
    prefixObservableApproxError μ h P (optimalPrefixDecision μ h P) =
      prefixScanError μ h P :=
  paper_scan_projection_address_bayes_optimality_seeds μ h P

end

end Omega.SPG.ScanProjectionBayesOptimality
