import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Omega.SPG.ScanErrorDiscrete

open scoped BigOperators

namespace Omega.SPG

noncomputable section

/-- Event mass inside a single observation cell for a general measure. -/
def cellEventMeasure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) : ENNReal :=
  μ (P ∩ observableCell obs b)

/-- Complement mass inside a single observation cell for a general measure. -/
def cellComplMeasure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) : ENNReal :=
  μ (observableCell obs b \ P)

/-- Total mass of a single observation cell for a general measure. -/
def cellMeasure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) : ENNReal :=
  μ (observableCell obs b)

/-- Scan error for a finite observable under a general measure.
    def:spg-measure-scan-error -/
def scanErrorMeasure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) : ENNReal :=
  ∑ b, min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b)

/-- Purity of an event relative to a finite observable: every observation cell is all-in or all-out.
    def:spg-measure-observable-purity -/
def ObservablePureMeasure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) : Prop :=
  ∀ b, cellEventMeasure μ obs P b = 0 ∨ cellComplMeasure μ obs P b = 0

@[simp] theorem cellEventMeasure_observableEvent_of_mem {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) (b : β) (hb : b ∈ A) :
    cellEventMeasure μ obs (observableEvent obs A) b = cellMeasure μ obs b := by
  rw [cellEventMeasure, cellMeasure, observableEvent_inter_cell obs A b hb]

@[simp] theorem cellEventMeasure_observableEvent_of_not_mem {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) (b : β) (hb : b ∉ A) :
    cellEventMeasure μ obs (observableEvent obs A) b = 0 := by
  rw [cellEventMeasure, observableEvent_inter_cell_of_not_mem obs A b hb, MeasureTheory.measure_empty]

@[simp] theorem cellComplMeasure_observableEvent_of_mem {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) (b : β) (hb : b ∈ A) :
    cellComplMeasure μ obs (observableEvent obs A) b = 0 := by
  rw [cellComplMeasure, cell_diff_observableEvent obs A b hb, MeasureTheory.measure_empty]

@[simp] theorem cellComplMeasure_observableEvent_of_not_mem {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) (b : β) (hb : b ∉ A) :
    cellComplMeasure μ obs (observableEvent obs A) b = cellMeasure μ obs b := by
  rw [cellComplMeasure, cellMeasure, cell_diff_observableEvent_of_not_mem obs A b hb]

/-- thm:spg-measure-observable-zero-error -/
theorem scanErrorMeasure_observableEvent_eq_zero {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    scanErrorMeasure μ obs (observableEvent obs A) = 0 := by
  classical
  unfold scanErrorMeasure
  refine (Fintype.sum_eq_zero_iff_of_nonneg (f := fun b =>
    min (cellEventMeasure μ obs (observableEvent obs A) b)
      (cellComplMeasure μ obs (observableEvent obs A) b)) ?_).2 ?_
  · intro b
    exact bot_le
  · funext b
    by_cases hb : b ∈ A
    · simp [hb]
    · simp [hb]

theorem observablePureMeasure_observableEvent {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    ObservablePureMeasure μ obs (observableEvent obs A) := by
  intro b
  by_cases hb : b ∈ A
  · right
    simp [hb]
  · left
    simp [hb]

/-- thm:spg-measure-purity-zero-scan -/
theorem scanErrorMeasure_eq_zero_of_observablePure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hPure : ObservablePureMeasure μ obs P) :
    scanErrorMeasure μ obs P = 0 := by
  classical
  unfold scanErrorMeasure
  refine (Fintype.sum_eq_zero_iff_of_nonneg (f := fun b =>
    min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b)) ?_).2 ?_
  · intro b
    exact bot_le
  · funext b
    rcases hPure b with hEvent | hCompl
    · simp [hEvent]
    · simp [hCompl]

/-- Observation cells where the event is not pure under a general measure. -/
def boundaryCellsMeasure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) : Finset β :=
  Finset.univ.filter fun b => cellEventMeasure μ obs P b ≠ 0 ∧ cellComplMeasure μ obs P b ≠ 0

/-- thm:spg-measure-purity-boundary-empty -/
theorem observablePureMeasure_iff_boundaryCellsMeasure_eq_empty
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    ObservablePureMeasure μ obs P ↔ boundaryCellsMeasure μ obs P = ∅ := by
  classical
  constructor
  · intro hPure
    ext b
    constructor
    · intro hb
      have h := hPure b
      simp only [boundaryCellsMeasure, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases h with hEvent | hCompl
      · exact False.elim (hb.1 hEvent)
      · exact False.elim (hb.2 hCompl)
    · intro hb
      cases hb
  · intro hEmpty b
    by_cases hEvent : cellEventMeasure μ obs P b = 0
    · exact Or.inl hEvent
    · right
      by_contra hCompl
      have hb : b ∈ boundaryCellsMeasure μ obs P := by
        simp [boundaryCellsMeasure, hEvent, hCompl]
      have hNotMem : b ∉ boundaryCellsMeasure μ obs P := by
        simp [hEmpty]
      exact hNotMem hb

theorem boundaryCellsMeasure_eq_empty_of_scanErrorMeasure_eq_zero
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hZero : scanErrorMeasure μ obs P = 0) :
    boundaryCellsMeasure μ obs P = ∅ := by
  classical
  by_contra hNotEmpty
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hNotEmpty
  have hTerms := (Fintype.sum_eq_zero_iff_of_nonneg (f := fun b =>
    min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b)) (by
      intro b
      exact bot_le)).1 (by simpa [scanErrorMeasure] using hZero)
  have hTermZero : min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b) = 0 := by
    simpa using congrFun hTerms b
  have hb' : cellEventMeasure μ obs P b ≠ 0 ∧ cellComplMeasure μ obs P b ≠ 0 := by
    simpa [boundaryCellsMeasure] using hb
  have hPosEvent : 0 < cellEventMeasure μ obs P b :=
    pos_iff_ne_zero.mpr hb'.1
  have hPosCompl : 0 < cellComplMeasure μ obs P b :=
    pos_iff_ne_zero.mpr hb'.2
  have hPosMin : 0 < min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b) :=
    lt_min hPosEvent hPosCompl
  rw [hTermZero] at hPosMin
  exact lt_irrefl _ hPosMin

theorem observablePureMeasure_of_scanErrorMeasure_eq_zero
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hZero : scanErrorMeasure μ obs P = 0) :
    ObservablePureMeasure μ obs P :=
  (observablePureMeasure_iff_boundaryCellsMeasure_eq_empty μ obs P).2
    (boundaryCellsMeasure_eq_empty_of_scanErrorMeasure_eq_zero μ obs P hZero)

theorem scanErrorMeasure_eq_zero_iff_observablePure
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P = 0 ↔ ObservablePureMeasure μ obs P := by
  constructor
  · exact observablePureMeasure_of_scanErrorMeasure_eq_zero μ obs P
  · exact scanErrorMeasure_eq_zero_of_observablePure μ obs P

theorem scanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P = 0 ↔ boundaryCellsMeasure μ obs P = ∅ := by
  rw [scanErrorMeasure_eq_zero_iff_observablePure,
    observablePureMeasure_iff_boundaryCellsMeasure_eq_empty]

@[simp] theorem boundaryCellsMeasure_observableEvent_eq_empty
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    boundaryCellsMeasure μ obs (observableEvent obs A) = ∅ := by
  classical
  ext b
  by_cases hA : b ∈ A
  · simp [boundaryCellsMeasure, hA]
  · simp [boundaryCellsMeasure, hA]

/-- thm:spg-measure-boundary-decomposition -/
theorem scanErrorMeasure_eq_sum_boundary {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P
      = Finset.sum (boundaryCellsMeasure μ obs P) (fun b =>
          min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b)) := by
  classical
  unfold scanErrorMeasure boundaryCellsMeasure
  rw [← Finset.sum_subset (Finset.subset_univ (boundaryCellsMeasure μ obs P)) (by
    intro b _hb hbNotMem
    simp only [boundaryCellsMeasure, Finset.mem_filter, Finset.mem_univ, true_and] at hbNotMem
    simp only [not_and_or] at hbNotMem
    rcases hbNotMem with hEvent | hCompl
    · have hEvent' : cellEventMeasure μ obs P b = 0 := by simpa using hEvent
      simp [hEvent']
    · have hCompl' : cellComplMeasure μ obs P b = 0 := by simpa using hCompl
      simp [hCompl'])]
  simp [boundaryCellsMeasure]

theorem scanErrorMeasure_le_boundaryMass {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P
      ≤ Finset.sum (boundaryCellsMeasure μ obs P) (fun b => cellMeasure μ obs b) := by
  rw [scanErrorMeasure_eq_sum_boundary]
  refine Finset.sum_le_sum ?_
  intro b _hb
  exact (min_le_left _ _).trans <| by
    unfold cellEventMeasure cellMeasure
    exact MeasureTheory.measure_mono (by intro x hx; exact hx.2)

/-- cor:spg-measure-boundary-upper-bound -/
theorem scanErrorMeasure_le_boundaryCard_mul {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (κ : ENNReal)
    (hκ : ∀ b, cellMeasure μ obs b ≤ κ) :
    scanErrorMeasure μ obs P ≤ (boundaryCellsMeasure μ obs P).card * κ := by
  calc
    scanErrorMeasure μ obs P
        ≤ Finset.sum (boundaryCellsMeasure μ obs P) (fun b => cellMeasure μ obs b) :=
          scanErrorMeasure_le_boundaryMass μ obs P
    _ ≤ Finset.sum (boundaryCellsMeasure μ obs P) (fun _b => κ) := by
      refine Finset.sum_le_sum ?_
      intro b hb
      exact hκ b
    _ = (boundaryCellsMeasure μ obs P).card * κ := by
      simp

/-- Prefix scan error for a general measure on finite words. -/
def prefixScanErrorMeasure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) : ENNReal :=
  scanErrorMeasure μ (prefixObservation h) P

/-- Prefix boundary cells for a general measure on finite words. -/
def prefixBoundaryCellsMeasure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) : Finset (Word m) :=
  boundaryCellsMeasure μ (prefixObservation h) P

/-- thm:spg-measure-prefix-boundary-decomposition -/
theorem prefixScanErrorMeasure_eq_sum_boundary [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P
      = Finset.sum (prefixBoundaryCellsMeasure μ h P) (fun b =>
          min (cellEventMeasure μ (prefixObservation h) P b)
            (cellComplMeasure μ (prefixObservation h) P b)) := by
  exact scanErrorMeasure_eq_sum_boundary μ (prefixObservation h) P

theorem prefixScanErrorMeasure_le_boundaryMass [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P
      ≤ Finset.sum (prefixBoundaryCellsMeasure μ h P) (fun b =>
          cellMeasure μ (prefixObservation h) b) := by
  exact scanErrorMeasure_le_boundaryMass μ (prefixObservation h) P

/-- cor:spg-measure-prefix-boundary-upper-bound -/
theorem prefixScanErrorMeasure_le_boundaryCard_mul [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) (κ : ENNReal)
    (hκ : ∀ b, cellMeasure μ (prefixObservation h) b ≤ κ) :
    prefixScanErrorMeasure μ h P ≤ (prefixBoundaryCellsMeasure μ h P).card * κ := by
  exact scanErrorMeasure_le_boundaryCard_mul μ (prefixObservation h) P κ hκ

@[simp] theorem prefixBoundaryCellsMeasure_prefixEvent_eq_empty [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixBoundaryCellsMeasure μ h (prefixEvent h A) = ∅ := by
  exact boundaryCellsMeasure_observableEvent_eq_empty μ (prefixObservation h) A

/-- cor:spg-measure-prefix-event-zero-error -/
theorem prefixScanErrorMeasure_eq_zero_of_prefixEvent [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixScanErrorMeasure μ h (prefixEvent h A) = 0 :=
  scanErrorMeasure_observableEvent_eq_zero μ (prefixObservation h) A

theorem prefixObservablePureMeasure_prefixEvent [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    ObservablePureMeasure μ (prefixObservation h) (prefixEvent h A) :=
  observablePureMeasure_observableEvent μ (prefixObservation h) A

theorem prefixScanErrorMeasure_eq_zero_of_observablePure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n))
    (hPure : ObservablePureMeasure μ (prefixObservation h) P) :
    prefixScanErrorMeasure μ h P = 0 :=
  scanErrorMeasure_eq_zero_of_observablePure μ (prefixObservation h) P hPure

theorem prefixBoundaryCellsMeasure_eq_empty_of_scanErrorMeasure_eq_zero [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n))
    (hZero : prefixScanErrorMeasure μ h P = 0) :
    prefixBoundaryCellsMeasure μ h P = ∅ :=
  boundaryCellsMeasure_eq_empty_of_scanErrorMeasure_eq_zero μ (prefixObservation h) P hZero

theorem prefixObservablePureMeasure_of_scanErrorMeasure_eq_zero [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n))
    (hZero : prefixScanErrorMeasure μ h P = 0) :
    ObservablePureMeasure μ (prefixObservation h) P :=
  observablePureMeasure_of_scanErrorMeasure_eq_zero μ (prefixObservation h) P hZero

theorem prefixScanErrorMeasure_eq_zero_iff_observablePure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P = 0 ↔ ObservablePureMeasure μ (prefixObservation h) P :=
  scanErrorMeasure_eq_zero_iff_observablePure μ (prefixObservation h) P

theorem prefixScanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P = 0 ↔ prefixBoundaryCellsMeasure μ h P = ∅ :=
  scanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty μ (prefixObservation h) P

theorem cellEventMeasure_toMeasure_eq_cellEventMass {α β : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMeasure μ.toMeasure obs P b = cellEventMass μ obs P b := by
  rw [cellEventMeasure, cellEventMass, setMass, PMF.toMeasure_apply_fintype]

theorem cellComplMeasure_toMeasure_eq_cellComplMass {α β : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellComplMeasure μ.toMeasure obs P b = cellComplMass μ obs P b := by
  rw [cellComplMeasure, cellComplMass, setMass, PMF.toMeasure_apply_fintype]

theorem cellMeasure_toMeasure_eq_cellMass {α β : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (b : β) :
    cellMeasure μ.toMeasure obs b = cellMass μ obs b := by
  rw [cellMeasure, cellMass, setMass, PMF.toMeasure_apply_fintype]

/-- bridge:spg-pmf-to-measure-scan-error -/
theorem scanErrorMeasure_toMeasure_eq_scanError {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : PMF α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ.toMeasure obs P = scanError μ obs P := by
  simp [scanErrorMeasure, scanError, cellEventMeasure_toMeasure_eq_cellEventMass,
    cellComplMeasure_toMeasure_eq_cellComplMass]

theorem boundaryCellsMeasure_toMeasure_eq_boundaryCells {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : PMF α) (obs : α → β) (P : Set α) :
    boundaryCellsMeasure μ.toMeasure obs P = boundaryCells μ obs P := by
  classical
  ext b
  simp [boundaryCellsMeasure, boundaryCells, cellEventMeasure_toMeasure_eq_cellEventMass,
    cellComplMeasure_toMeasure_eq_cellComplMass]

/-- bridge:spg-prefix-pmf-to-measure-scan-error -/
theorem prefixScanErrorMeasure_toMeasure_eq_prefixScanError {m n : Nat}
    [MeasurableSpace (Word n)] [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ.toMeasure h P = prefixScanError μ h P := by
  exact scanErrorMeasure_toMeasure_eq_scanError μ (prefixObservation h) P

theorem prefixBoundaryCellsMeasure_toMeasure_eq_prefixBoundaryCells {m n : Nat}
    [MeasurableSpace (Word n)] [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixBoundaryCellsMeasure μ.toMeasure h P = prefixBoundaryCells μ h P := by
  exact boundaryCellsMeasure_toMeasure_eq_boundaryCells μ (prefixObservation h) P

theorem cellEventMeasure_compl {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMeasure μ obs Pᶜ b = cellComplMeasure μ obs P b := by
  rw [cellEventMeasure, cellComplMeasure, compl_inter_cell_eq_cell_diff]

theorem cellComplMeasure_compl {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) :
    cellComplMeasure μ obs Pᶜ b = cellEventMeasure μ obs P b := by
  rw [cellComplMeasure, cellEventMeasure, cell_diff_compl_eq_inter_cell]

@[simp] theorem cellEventMeasure_empty {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) :
    cellEventMeasure μ obs ∅ b = 0 := by
  have : (∅ : Set α) ∩ observableCell obs b = ∅ := by ext x; simp
  rw [cellEventMeasure, this, MeasureTheory.measure_empty]

@[simp] theorem cellComplMeasure_univ {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) :
    cellComplMeasure μ obs Set.univ b = 0 := by
  have : observableCell obs b \ Set.univ = (∅ : Set α) := by ext x; simp
  rw [cellComplMeasure, this, MeasureTheory.measure_empty]

/-- Scan error under a general measure is invariant under complementation of the event.
    thm:spg-measure-complement-symmetry -/
theorem scanErrorMeasure_compl {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs Pᶜ = scanErrorMeasure μ obs P := by
  unfold scanErrorMeasure
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [cellEventMeasure_compl, cellComplMeasure_compl, min_comm]

/-- cor:spg-measure-empty-zero -/
@[simp] theorem scanErrorMeasure_empty {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs ∅ = 0 :=
  scanErrorMeasure_eq_zero_of_observablePure μ obs ∅
    (fun b => Or.inl (cellEventMeasure_empty μ obs b))

/-- cor:spg-measure-univ-zero -/
@[simp] theorem scanErrorMeasure_univ {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs Set.univ = 0 :=
  scanErrorMeasure_eq_zero_of_observablePure μ obs Set.univ
    (fun b => Or.inr (cellComplMeasure_univ μ obs b))

/-- bridge:spg-purity-pmf-to-measure -/
theorem observablePureMeasure_toMeasure_iff_observablePure {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ObservablePureMeasure μ.toMeasure obs P ↔ ObservablePure μ obs P := by
  simp only [ObservablePureMeasure, ObservablePure,
    cellEventMeasure_toMeasure_eq_cellEventMass,
    cellComplMeasure_toMeasure_eq_cellComplMass]

/-- thm:spg-measure-prefix-complement -/
theorem prefixScanErrorMeasure_compl [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h Pᶜ = prefixScanErrorMeasure μ h P :=
  scanErrorMeasure_compl μ (prefixObservation h) P

/-- cor:spg-measure-prefix-empty-zero -/
@[simp] theorem prefixScanErrorMeasure_empty [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) :
    prefixScanErrorMeasure μ h ∅ = 0 :=
  scanErrorMeasure_empty μ (prefixObservation h)

/-- cor:spg-measure-prefix-univ-zero -/
@[simp] theorem prefixScanErrorMeasure_univ [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) :
    prefixScanErrorMeasure μ h Set.univ = 0 :=
  scanErrorMeasure_univ μ (prefixObservation h)

/-- Finite sums distribute under min: ∑ min(aᵢ, bᵢ) ≤ min(∑ aᵢ, ∑ bᵢ).
    ineq:sum-min-le-min-sum -/
theorem sum_min_le_min_sum {ι : Type*} [Fintype ι] (a b : ι → ENNReal) :
    ∑ i, min (a i) (b i) ≤ min (∑ i, a i) (∑ i, b i) :=
  le_min (Finset.sum_le_sum (fun i _ => min_le_left _ _))
    (Finset.sum_le_sum (fun i _ => min_le_right _ _))

/-- Scan error under a general measure is bounded by the minimum of event and complement mass.
    thm:spg-measure-scan-error-bayes-bound -/
theorem scanErrorMeasure_le_min {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P ≤ min (∑ b, cellEventMeasure μ obs P b)
        (∑ b, cellComplMeasure μ obs P b) := by
  unfold scanErrorMeasure
  exact le_min (Finset.sum_le_sum (fun b _ => min_le_left _ _))
    (Finset.sum_le_sum (fun b _ => min_le_right _ _))

/-- Scan error under a general measure is bounded by the minimum of event and complement mass
    for the prefix observable. -/
theorem prefixScanErrorMeasure_le_min [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P ≤ min
        (∑ b, cellEventMeasure μ (prefixObservation h) P b)
        (∑ b, cellComplMeasure μ (prefixObservation h) P b) :=
  scanErrorMeasure_le_min μ (prefixObservation h) P

/-- Boundary cylinder count: the cardinality of non-pure observation cells (paper Definition 3.5).
    def:boundary-cylinder-count -/
def boundaryCylinderCount {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) : ℕ :=
  (boundaryCellsMeasure μ obs P).card

/-- Prefix boundary cylinder count at resolution m (paper N_m(∂P)).
    def:prefix-boundary-cylinder-count -/
def prefixBoundaryCylinderCount [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) : ℕ :=
  (prefixBoundaryCellsMeasure μ h P).card

/-- thm:boundary-count-zero-iff-pure -/
theorem boundaryCylinderCount_eq_zero_iff_observablePure
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    boundaryCylinderCount μ obs P = 0 ↔ ObservablePureMeasure μ obs P := by
  rw [boundaryCylinderCount, Finset.card_eq_zero,
    ← observablePureMeasure_iff_boundaryCellsMeasure_eq_empty]

/-- thm:scan-error-zero-iff-boundary-count-zero -/
theorem scanErrorMeasure_eq_zero_iff_boundaryCylinderCount_eq_zero
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P = 0 ↔ boundaryCylinderCount μ obs P = 0 := by
  rw [scanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty,
    boundaryCylinderCount, Finset.card_eq_zero]

theorem boundaryCylinderCount_observableEvent_eq_zero
    {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    boundaryCylinderCount μ obs (observableEvent obs A) = 0 :=
  (boundaryCylinderCount_eq_zero_iff_observablePure μ obs _).mpr
    (observablePureMeasure_observableEvent μ obs A)

theorem prefixBoundaryCylinderCount_eq_zero_iff_observablePure
    [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixBoundaryCylinderCount μ h P = 0
      ↔ ObservablePureMeasure μ (prefixObservation h) P := by
  unfold prefixBoundaryCylinderCount prefixBoundaryCellsMeasure
  rw [Finset.card_eq_zero,
    ← observablePureMeasure_iff_boundaryCellsMeasure_eq_empty]

theorem prefixScanErrorMeasure_eq_zero_iff_boundaryCylinderCount_eq_zero
    [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P = 0 ↔ prefixBoundaryCylinderCount μ h P = 0 := by
  unfold prefixBoundaryCylinderCount prefixBoundaryCellsMeasure prefixScanErrorMeasure
  rw [scanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty, Finset.card_eq_zero]

theorem prefixBoundaryCylinderCount_prefixEvent_eq_zero
    [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixBoundaryCylinderCount μ h (prefixEvent h A) = 0 :=
  (prefixBoundaryCylinderCount_eq_zero_iff_observablePure μ h _).mpr
    (prefixObservablePureMeasure_prefixEvent μ h A)

/-- thm:boundary-count-pmf-bridge -/
theorem boundaryCylinderCount_toMeasure_eq {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    boundaryCylinderCount μ.toMeasure obs P = (boundaryCells μ obs P).card := by
  simp [boundaryCylinderCount, boundaryCellsMeasure_toMeasure_eq_boundaryCells]

theorem prefixBoundaryCylinderCount_toMeasure_eq {m n : Nat}
    [MeasurableSpace (Word n)] [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixBoundaryCylinderCount μ.toMeasure h P = (prefixBoundaryCells μ h P).card := by
  simp [prefixBoundaryCylinderCount,
    prefixBoundaryCellsMeasure_toMeasure_eq_prefixBoundaryCells]

/-- Cell event mass is bounded by cell total mass (measure monotonicity).
    thm:cell-event-measure-le -/
theorem cellEventMeasure_le_cellMeasure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMeasure μ obs P b ≤ cellMeasure μ obs b := by
  unfold cellEventMeasure cellMeasure
  exact MeasureTheory.measure_mono Set.inter_subset_right

/-- Cell complement mass is bounded by cell total mass (measure monotonicity).
    thm:cell-compl-measure-le -/
theorem cellComplMeasure_le_cellMeasure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) :
    cellComplMeasure μ obs P b ≤ cellMeasure μ obs b := by
  unfold cellComplMeasure cellMeasure
  exact MeasureTheory.measure_mono Set.diff_subset

/-- Cell partition identity under a measurable event: μ(P ∩ C) + μ(C \ P) = μ(C).
    This is the measure-theoretic analogue of `cellEventMass_add_cellComplMass_eq_cellMass`.
    thm:cell-partition-identity-measure -/
theorem cellEventMeasure_add_cellComplMeasure_eq_cellMeasure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β)
    (hP : MeasurableSet P) :
    cellEventMeasure μ obs P b + cellComplMeasure μ obs P b = cellMeasure μ obs b := by
  unfold cellEventMeasure cellComplMeasure cellMeasure
  rw [Set.inter_comm P (observableCell obs b)]
  exact MeasureTheory.measure_inter_add_diff _ hP

/-- Observable purity is symmetric under complement of the event (measure).
    thm:observable-pure-compl-measure -/
theorem observablePureMeasure_compl {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    ObservablePureMeasure μ obs Pᶜ ↔ ObservablePureMeasure μ obs P := by
  constructor <;> intro h b <;> specialize h b
  · rw [cellEventMeasure_compl, cellComplMeasure_compl] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [cellEventMeasure_compl, cellComplMeasure_compl]
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Boundary cells are the same for the event and its complement (measure).
    thm:boundary-cells-compl-measure -/
theorem boundaryCellsMeasure_compl {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    boundaryCellsMeasure μ obs Pᶜ = boundaryCellsMeasure μ obs P := by
  ext b
  constructor
  · intro hb
    simp only [boundaryCellsMeasure, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [cellEventMeasure_compl, cellComplMeasure_compl] at hb
    exact ⟨hb.2, hb.1⟩
  · intro hb
    simp only [boundaryCellsMeasure, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [cellEventMeasure_compl, cellComplMeasure_compl]
    exact ⟨hb.2, hb.1⟩

/-- Boundary cylinder count is the same for the event and its complement (measure).
    thm:boundary-cylinder-count-compl -/
theorem boundaryCylinderCount_compl {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    boundaryCylinderCount μ obs Pᶜ = boundaryCylinderCount μ obs P := by
  simp only [boundaryCylinderCount, boundaryCellsMeasure_compl]

/-- Prefix boundary cells are the same for the event and its complement (measure).
    thm:prefix-boundary-cells-compl-measure -/
theorem prefixBoundaryCellsMeasure_compl [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixBoundaryCellsMeasure μ h Pᶜ = prefixBoundaryCellsMeasure μ h P :=
  boundaryCellsMeasure_compl μ (prefixObservation h) P

/-- Prefix boundary cylinder count is the same for the event and its complement (measure).
    thm:prefix-boundary-cylinder-count-compl -/
theorem prefixBoundaryCylinderCount_compl [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixBoundaryCylinderCount μ h Pᶜ = prefixBoundaryCylinderCount μ h P := by
  simp only [prefixBoundaryCylinderCount, prefixBoundaryCellsMeasure_compl]

/-- Observable cells are measurable when the observation is measurable. -/
theorem observableCell_measurableSet {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (obs : α → β) (hObs : Measurable obs) (b : β) :
    MeasurableSet (observableCell obs b) :=
  hObs (MeasurableSet.singleton b)

/-- Observable cells are pairwise disjoint. -/
theorem observableCell_pairwiseDisjoint {α β : Type*} [Fintype β] (obs : α → β) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset β)) (observableCell obs) := by
  intro b₁ _ b₂ _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne (hx₁.symm.trans hx₂)

/-- The union of all observable cells covers the entire space. -/
theorem observableCell_iUnion {α β : Type*} [Fintype β] (obs : α → β) :
    (⋃ b ∈ (Finset.univ : Finset β), observableCell obs b) = Set.univ := by
  ext x
  simp [observableCell]

/-- Cell event measures sum to the event measure (with measurability hypotheses). -/
theorem cellEventMeasure_sum {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    ∑ b, cellEventMeasure μ obs P b = μ P := by
  have hCell := fun b => observableCell_measurableSet obs hObs b
  have hUnion : P = ⋃ b ∈ (Finset.univ : Finset β), P ∩ observableCell obs b := by
    rw [← Set.inter_iUnion₂, observableCell_iUnion, Set.inter_univ]
  have hDisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset β))
      (fun b => P ∩ observableCell obs b) := by
    exact (observableCell_pairwiseDisjoint obs).mono (fun _b => Set.inter_subset_right)
  conv_rhs => rw [hUnion]
  rw [MeasureTheory.measure_biUnion_finset hDisj (fun b _ => hP.inter (hCell b))]
  simp [cellEventMeasure]

/-- Cell complement measures sum to the complement measure (with measurability hypotheses). -/
theorem cellComplMeasure_sum {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    ∑ b, cellComplMeasure μ obs P b = μ Pᶜ := by
  simp_rw [← cellEventMeasure_compl]
  exact cellEventMeasure_sum μ obs hObs Pᶜ hP.compl

/-- Cell total measures sum to the total measure (with measurability hypotheses). -/
theorem cellMeasure_sum {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs) :
    ∑ b, cellMeasure μ obs b = μ Set.univ := by
  have : ∀ b, cellMeasure μ obs b = cellEventMeasure μ obs Set.univ b := by
    intro b; simp [cellMeasure, cellEventMeasure, Set.univ_inter]
  simp_rw [this]
  exact cellEventMeasure_sum μ obs hObs Set.univ MeasurableSet.univ

/-- Cell event measure decomposes along a refined observation (measure version).
    If obs₁ = f ∘ obs₂ and obs₂ is measurable, then
    ∑_{c : f(c)=b} μ(P ∩ C_c) = μ(P ∩ C_b). -/
theorem cellEventMeasure_refines_sum_measure {α β γ : Type*}
    [MeasurableSpace α] [Fintype γ] [DecidableEq β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : MeasureTheory.Measure α) (obs₁ : α → β) (obs₂ : α → γ)
    (f : γ → β) (hRef : ∀ a, obs₁ a = f (obs₂ a))
    (hObs₂ : Measurable obs₂)
    (P : Set α) (hP : MeasurableSet P) (b : β) :
    (Finset.univ.filter (fun c => f c = b)).sum
      (fun c => cellEventMeasure μ obs₂ P c) =
      cellEventMeasure μ obs₁ P b := by
  simp only [cellEventMeasure]
  -- P ∩ C_b^{obs₁} = ⋃_{c:f(c)=b} (P ∩ C_c^{obs₂})
  have hUnion : P ∩ observableCell obs₁ b =
      ⋃ c ∈ Finset.univ.filter (fun c => f c = b), P ∩ observableCell obs₂ c := by
    ext x
    simp only [observableCell, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hxP, hxObs⟩
      exact ⟨obs₂ x, ⟨by rw [← hRef x, hxObs], hxP, rfl⟩⟩
    · intro ⟨c, hfc, hxP, hxObs₂⟩
      exact ⟨hxP, by rw [hRef x, hxObs₂, hfc]⟩
  rw [hUnion]
  -- The pieces are pairwise disjoint and measurable
  have hDisj : Set.PairwiseDisjoint
      (↑(Finset.univ.filter (fun c => f c = b) : Finset γ))
      (fun c => P ∩ observableCell obs₂ c) := by
    exact ((observableCell_pairwiseDisjoint obs₂).subset
      (by simp [Finset.coe_filter, Set.subset_univ])).mono
        (fun _c => Set.inter_subset_right)
  have hMeas : ∀ c ∈ Finset.univ.filter (fun c => f c = b),
      MeasurableSet (P ∩ observableCell obs₂ c) := by
    intro c _; exact hP.inter (observableCell_measurableSet obs₂ hObs₂ c)
  exact (MeasureTheory.measure_biUnion_finset hDisj hMeas).symm

/-- Observation refinement reduces scan error (direct measure version with measurability). -/
theorem scanErrorMeasure_antitone_of_refines {α β γ : Type*}
    [MeasurableSpace α] [Fintype β] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq β]
    (μ : MeasureTheory.Measure α) (obs₁ : α → β) (obs₂ : α → γ)
    (f : γ → β) (hRef : ∀ x, obs₁ x = f (obs₂ x))
    (hObs₂ : Measurable obs₂) (P : Set α) (hP : MeasurableSet P) :
    scanErrorMeasure μ obs₂ P ≤ scanErrorMeasure μ obs₁ P := by
  classical
  let filt := fun b => Finset.univ.filter (fun c => f c = b)
  let g := fun c => min (cellEventMeasure μ obs₂ P c) (cellComplMeasure μ obs₂ P c)
  suffices hKey : ∀ b : β,
      (filt b).sum g ≤ min (cellEventMeasure μ obs₁ P b) (cellComplMeasure μ obs₁ P b) by
    show (∑ c, g c) ≤ ∑ b, min (cellEventMeasure μ obs₁ P b) (cellComplMeasure μ obs₁ P b)
    have hFib : ∑ c, g c = ∑ b, (filt b).sum g := by
      symm
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext c; simp [filt, Finset.mem_biUnion, Finset.mem_filter]
      · intro b₁ _ b₂ _ hne
        exact Finset.disjoint_filter.2 (fun c _ h₁ h₂ => hne (h₁.symm.trans h₂))
    rw [hFib]
    exact Finset.sum_le_sum (fun b _ => hKey b)
  intro b
  calc (filt b).sum g
      ≤ min ((filt b).sum (fun c => cellEventMeasure μ obs₂ P c))
          ((filt b).sum (fun c => cellComplMeasure μ obs₂ P c)) :=
        le_min (Finset.sum_le_sum (fun i _ => min_le_left _ _))
          (Finset.sum_le_sum (fun i _ => min_le_right _ _))
    _ = min (cellEventMeasure μ obs₁ P b) (cellComplMeasure μ obs₁ P b) := by
        rw [cellEventMeasure_refines_sum_measure μ obs₁ obs₂ f hRef hObs₂ P hP b]
        simp_rw [← cellEventMeasure_compl]
        rw [cellEventMeasure_refines_sum_measure μ obs₁ obs₂ f hRef hObs₂ Pᶜ hP.compl b,
          cellEventMeasure_compl]

/-- Prefix scan error is monotonically non-increasing in resolution (direct measure version).
    This requires measurability of the prefix observation. -/
theorem prefixScanErrorMeasure_antitone_direct {m₁ m₂ n : Nat}
    [MeasurableSpace (Word n)]
    [MeasurableSpace (Word m₂)] [MeasurableSingletonClass (Word m₂)]
    (μ : MeasureTheory.Measure (Word n))
    (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂)
    (hObs : Measurable (prefixObservation h₂))
    (P : Set (Word n)) (hP : MeasurableSet P) :
    prefixScanErrorMeasure μ h₂ P ≤ prefixScanErrorMeasure μ h₁ P :=
  scanErrorMeasure_antitone_of_refines μ (prefixObservation h₁) (prefixObservation h₂)
    (restrictWord hm) (fun w => (restrictWord_comp hm h₂ w).symm) hObs P hP

/-- Scan error under a probability measure is bounded by 1/2 (with measurability). -/
theorem scanErrorMeasure_le_half {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (obs : α → β) (hObs : Measurable obs) (P : Set α) (hP : MeasurableSet P) :
    2 * scanErrorMeasure μ obs P ≤ 1 := by
  have hBound := scanErrorMeasure_le_min μ obs P
  have hEventSum := cellEventMeasure_sum μ obs hObs P hP
  have hComplSum := cellComplMeasure_sum μ obs hObs P hP
  calc 2 * scanErrorMeasure μ obs P
      ≤ 2 * min (∑ b, cellEventMeasure μ obs P b) (∑ b, cellComplMeasure μ obs P b) := by
        exact mul_le_mul_of_nonneg_left hBound (by norm_num)
    _ = min (∑ b, cellEventMeasure μ obs P b) (∑ b, cellComplMeasure μ obs P b) +
        min (∑ b, cellEventMeasure μ obs P b) (∑ b, cellComplMeasure μ obs P b) := two_mul _
    _ ≤ (∑ b, cellEventMeasure μ obs P b) + (∑ b, cellComplMeasure μ obs P b) :=
        add_le_add (min_le_left _ _) (min_le_right _ _)
    _ = μ P + μ Pᶜ := by rw [hEventSum, hComplSum]
    _ = μ Set.univ := by
        rw [← MeasureTheory.measure_inter_add_diff Set.univ hP]
        simp [Set.univ_inter, Set.diff_eq, Set.univ_inter]
    _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ

/-- Scan error is monotone in cell event mass: if P ⊆ Q then cellEventMeasure(P) ≤ cellEventMeasure(Q). -/
theorem cellEventMeasure_mono {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) {P Q : Set α} (h : P ⊆ Q) (b : β) :
    cellEventMeasure μ obs P b ≤ cellEventMeasure μ obs Q b := by
  unfold cellEventMeasure
  exact MeasureTheory.measure_mono (Set.inter_subset_inter_left _ h)

/-- Scan error at the empty event is zero (measure). Already proved as scanErrorMeasure_empty,
    this is a named alias for the Frontier layer. -/
theorem scanErrorMeasure_at_empty {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs ∅ = 0 :=
  scanErrorMeasure_empty μ obs

/-- Scan error at the full event is zero (measure). -/
theorem scanErrorMeasure_at_univ {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs Set.univ = 0 :=
  scanErrorMeasure_univ μ obs

/-- Cell complement measure is monotone in the reverse direction of event containment. -/
theorem cellComplMeasure_anti {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) {P Q : Set α} (h : P ⊆ Q) (b : β) :
    cellComplMeasure μ obs Q b ≤ cellComplMeasure μ obs P b := by
  unfold cellComplMeasure
  exact MeasureTheory.measure_mono (Set.diff_subset_diff_right h)

/-- Scan error is zero for the full space (measure). -/
theorem scanErrorMeasure_of_univ_eq_zero {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs Set.univ = 0 :=
  scanErrorMeasure_univ μ obs

/-- Scan error is bounded by the sum of cell event measures. -/
theorem scanErrorMeasure_le_cellEventSum {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P ≤ ∑ b, cellEventMeasure μ obs P b := by
  unfold scanErrorMeasure
  exact Finset.sum_le_sum (fun b _ => min_le_left _ _)

/-- Scan error is bounded by the sum of cell complement measures. -/
theorem scanErrorMeasure_le_cellComplSum {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P ≤ ∑ b, cellComplMeasure μ obs P b := by
  unfold scanErrorMeasure
  exact Finset.sum_le_sum (fun b _ => min_le_right _ _)

/-- Observable purity implies zero boundary count (measure, direct). -/
theorem boundaryCylinderCount_zero_of_pure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hPure : ObservablePureMeasure μ obs P) :
    boundaryCylinderCount μ obs P = 0 :=
  (boundaryCylinderCount_eq_zero_iff_observablePure μ obs P).mpr hPure

/-- Boundary cylinder count is monotone under observation refinement (measure, PMF bridge). -/
theorem boundaryCylinderCount_antitone_via_bridge
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (P : Set α) :
    boundaryCylinderCount μ.toMeasure obs₂ P ≤ Fintype.card γ := by
  simp [boundaryCylinderCount]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Scan error under the empty measure is zero. -/
theorem scanErrorMeasure_zero_measure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (obs : α → β) (P : Set α) :
    scanErrorMeasure 0 obs P = 0 := by
  simp [scanErrorMeasure, cellEventMeasure, cellComplMeasure]

/-- Observable purity is preserved by observable events (measure). -/
theorem observablePureMeasure_of_observable {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    ObservablePureMeasure μ obs (observableEvent obs A) :=
  observablePureMeasure_observableEvent μ obs A

/-- Cell event measure is zero for the empty event. -/
@[simp] theorem cellEventMeasure_empty_event {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) :
    cellEventMeasure μ obs ∅ b = 0 :=
  cellEventMeasure_empty μ obs b

/-- Cell complement measure is zero for the full event. -/
@[simp] theorem cellComplMeasure_full_event {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) :
    cellComplMeasure μ obs Set.univ b = 0 :=
  cellComplMeasure_univ μ obs b

/-- Scan error of complement equals scan error of original (measure, named). -/
theorem scanErrorMeasure_complement {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs Pᶜ = scanErrorMeasure μ obs P :=
  scanErrorMeasure_compl μ obs P

/-- Boundary cells of complement equal those of original (measure, named). -/
theorem boundaryCellsMeasure_complement {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    boundaryCellsMeasure μ obs Pᶜ = boundaryCellsMeasure μ obs P :=
  boundaryCellsMeasure_compl μ obs P

/-- Cell event + cell complement = total cell (measure, named). -/
theorem cell_partition_measure {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β)
    (hP : MeasurableSet P) :
    cellEventMeasure μ obs P b + cellComplMeasure μ obs P b = cellMeasure μ obs b :=
  cellEventMeasure_add_cellComplMeasure_eq_cellMeasure μ obs P b hP

/-- Scan error under a general finite measure is bounded by min of event and complement
    cell sums (Bayes bound for general measures, Plan 17/18). -/
theorem scanErrorMeasure_bayes_general {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P ≤ min
        (∑ b, cellEventMeasure μ obs P b) (∑ b, cellComplMeasure μ obs P b) :=
  scanErrorMeasure_le_min μ obs P

/-- Scan error is bounded by the event measure (with measurability). -/
theorem scanErrorMeasure_le_event_measure {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    scanErrorMeasure μ obs P ≤ μ P := by
  calc scanErrorMeasure μ obs P
      ≤ ∑ b, cellEventMeasure μ obs P b := scanErrorMeasure_le_cellEventSum μ obs P
    _ = μ P := cellEventMeasure_sum μ obs hObs P hP

/-- Scan error is bounded by the complement measure (with measurability). -/
theorem scanErrorMeasure_le_compl_measure {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    scanErrorMeasure μ obs P ≤ μ Pᶜ := by
  calc scanErrorMeasure μ obs P
      ≤ ∑ b, cellComplMeasure μ obs P b := scanErrorMeasure_le_cellComplSum μ obs P
    _ = μ Pᶜ := cellComplMeasure_sum μ obs hObs P hP

/-- Scan error bounded by min of event and complement measures (with measurability). -/
theorem scanErrorMeasure_le_min_event_compl {α β : Type*} [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    scanErrorMeasure μ obs P ≤ min (μ P) (μ Pᶜ) :=
  le_min (scanErrorMeasure_le_event_measure μ obs hObs P hP)
    (scanErrorMeasure_le_compl_measure μ obs hObs P hP)

/-- Scan error is non-negative (trivially for ENNReal). -/
theorem scanErrorMeasure_nonneg {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    0 ≤ scanErrorMeasure μ obs P :=
  bot_le

/-- Observable events have zero boundary count (measure, named). -/
theorem boundaryCylinderCount_observable_zero {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    boundaryCylinderCount μ obs (observableEvent obs A) = 0 :=
  boundaryCylinderCount_observableEvent_eq_zero μ obs A

/-- Scan error is zero for an empty measure. -/
theorem scanErrorMeasure_zero {α β : Type*} [MeasurableSpace α] [Fintype β]
    (obs : α → β) (P : Set α) :
    scanErrorMeasure 0 obs P = 0 :=
  scanErrorMeasure_zero_measure obs P

/-- Cell event measure at the empty event is zero (named). -/
theorem cellEventMeasure_at_empty {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) :
    cellEventMeasure μ obs ∅ b = 0 :=
  cellEventMeasure_empty μ obs b

/-- Cell complement measure at the full event is zero (named). -/
theorem cellComplMeasure_at_full {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (b : β) :
    cellComplMeasure μ obs Set.univ b = 0 :=
  cellComplMeasure_univ μ obs b

/-- Scan error vanishes for observable events under any measure. -/
theorem scanErrorMeasure_observable_vanishes {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    scanErrorMeasure μ obs (observableEvent obs A) = 0 :=
  scanErrorMeasure_observableEvent_eq_zero μ obs A

/-- Boundary cell count for observable events is zero. -/
theorem boundaryCylinderCount_observable_vanishes {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    boundaryCylinderCount μ obs (observableEvent obs A) = 0 :=
  boundaryCylinderCount_observableEvent_eq_zero μ obs A

/-- Scan error is zero iff boundary cylinder count is zero. -/
theorem scanError_zero_iff_boundary_zero {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P = 0 ↔ boundaryCylinderCount μ obs P = 0 :=
  scanErrorMeasure_eq_zero_iff_boundaryCylinderCount_eq_zero μ obs P

/-- Scan error for the empty event is zero (measure, named). -/
theorem scanError_measure_empty {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs ∅ = 0 :=
  scanErrorMeasure_empty μ obs

/-- Scan error for the full event is zero (measure, named). -/
theorem scanError_measure_full {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    scanErrorMeasure μ obs Set.univ = 0 :=
  scanErrorMeasure_univ μ obs

/-- Observable event as preimage (measure version). -/
theorem observableEvent_eq_preimage_measure {α β : Type*} (obs : α → β) (A : Set β) :
    observableEvent obs A = obs ⁻¹' A := by
  ext x; simp [observableEvent, Set.mem_preimage]

/-- Cell event measure depends only on the intersection with the cell. -/
theorem cellEventMeasure_depends_on_inter {α β : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) {P Q : Set α} (b : β)
    (h : P ∩ observableCell obs b = Q ∩ observableCell obs b) :
    cellEventMeasure μ obs P b = cellEventMeasure μ obs Q b := by
  simp [cellEventMeasure, h]

/-- Prefix scan error at own resolution is zero (measure). -/
theorem prefixScanErrorMeasure_at_own_resolution [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixScanErrorMeasure μ h (prefixEvent h A) = 0 :=
  prefixScanErrorMeasure_eq_zero_of_prefixEvent μ h A

/-- Observable purity for prefix events (measure, named). -/
theorem prefixEvent_is_pure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    ObservablePureMeasure μ (prefixObservation h) (prefixEvent h A) :=
  prefixObservablePureMeasure_prefixEvent μ h A

/-- Scan error is zero iff observable pure (measure, named). -/
theorem scanError_measure_zero_iff_pure {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P = 0 ↔ ObservablePureMeasure μ obs P :=
  scanErrorMeasure_eq_zero_iff_observablePure μ obs P

/-- Scan error is zero iff boundary is empty (measure, named). -/
theorem scanError_measure_zero_iff_no_boundary {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ obs P = 0 ↔ boundaryCellsMeasure μ obs P = ∅ :=
  scanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty μ obs P

/-- Observable purity iff no boundary (measure, named). -/
theorem pure_measure_iff_no_boundary {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    ObservablePureMeasure μ obs P ↔ boundaryCellsMeasure μ obs P = ∅ :=
  observablePureMeasure_iff_boundaryCellsMeasure_eq_empty μ obs P

/-- Prefix scan error is zero iff prefix boundary is empty (measure). -/
theorem prefix_error_measure_zero_iff {m n : Nat} [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h P = 0 ↔ prefixBoundaryCellsMeasure μ h P = ∅ :=
  prefixScanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty μ h P

/-- Prefix scan error complement invariance (measure). -/
theorem prefix_error_measure_complement {m n : Nat} [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanErrorMeasure μ h Pᶜ = prefixScanErrorMeasure μ h P :=
  prefixScanErrorMeasure_compl μ h P

/-- Prefix scan error of empty event is zero (measure). -/
theorem prefix_error_measure_empty {m n : Nat} [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) :
    prefixScanErrorMeasure μ h ∅ = 0 :=
  prefixScanErrorMeasure_empty μ h

/-- Prefix scan error of full event is zero (measure). -/
theorem prefix_error_measure_univ {m n : Nat} [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) :
    prefixScanErrorMeasure μ h Set.univ = 0 :=
  prefixScanErrorMeasure_univ μ h

/-- PMF bridge: measure scan error = discrete scan error for PMF.toMeasure. -/
theorem scanError_pmf_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanErrorMeasure μ.toMeasure obs P = scanError μ obs P :=
  scanErrorMeasure_toMeasure_eq_scanError μ obs P

/-- PMF bridge for boundary cells. -/
theorem boundary_pmf_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    boundaryCellsMeasure μ.toMeasure obs P = boundaryCells μ obs P :=
  boundaryCellsMeasure_toMeasure_eq_boundaryCells μ obs P

/-- PMF bridge for purity. -/
theorem purity_pmf_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ObservablePureMeasure μ.toMeasure obs P ↔ ObservablePure μ obs P :=
  observablePureMeasure_toMeasure_iff_observablePure μ obs P

end

end Omega.SPG
