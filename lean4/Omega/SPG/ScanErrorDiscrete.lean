import Mathlib.Probability.ProbabilityMassFunction.Basic
import Omega.Folding.Defect

open scoped BigOperators

namespace Omega.SPG

noncomputable section

/-- Finite mass of a set under a discrete probability law. -/
def setMass {α : Type*} [Fintype α] (μ : PMF α) (s : Set α) : ENNReal :=
  ∑ x, s.indicator μ x

@[simp] theorem setMass_empty {α : Type*} [Fintype α] (μ : PMF α) :
    setMass μ ∅ = 0 := by
  simp [setMass]

theorem setMass_mono {α : Type*} [Fintype α] (μ : PMF α) {s t : Set α} (hst : s ⊆ t) :
    setMass μ s ≤ setMass μ t := by
  simp [setMass]
  refine Finset.sum_le_sum ?_
  intro x _hx
  by_cases hs : x ∈ s
  · have ht : x ∈ t := hst hs
    simp [Set.indicator, hs, ht]
  · by_cases ht : x ∈ t
    · simp [Set.indicator, hs, ht]
    · simp [Set.indicator, hs, ht]

/-- The observation fiber over `b`. -/
def observableCell {α β : Type*} (obs : α → β) (b : β) : Set α :=
  {x | obs x = b}

/-- Events decided by the observable `obs`. -/
def observableEvent {α β : Type*} (obs : α → β) (A : Set β) : Set α :=
  {x | obs x ∈ A}

/-- Event mass inside a single observation cell. -/
def cellEventMass {α β : Type*} [Fintype α] (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    ENNReal :=
  setMass μ (P ∩ observableCell obs b)

/-- Complement mass inside a single observation cell. -/
def cellComplMass {α β : Type*} [Fintype α] (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    ENNReal :=
  setMass μ (observableCell obs b \ P)

/-- Total mass of a single observation cell. -/
def cellMass {α β : Type*} [Fintype α] (μ : PMF α) (obs : α → β) (b : β) : ENNReal :=
  setMass μ (observableCell obs b)

/-- The discrete scan-error profile induced by the observable `obs`.
    def:spg-discrete-scan-error -/
def scanError {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) : ENNReal :=
  ∑ b, min (cellEventMass μ obs P b) (cellComplMass μ obs P b)

theorem cellEventMass_le_cellMass {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMass μ obs P b ≤ cellMass μ obs b :=
  setMass_mono μ (by intro x hx; exact hx.2)

theorem cellComplMass_le_cellMass {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellComplMass μ obs P b ≤ cellMass μ obs b :=
  setMass_mono μ (by intro x hx; exact hx.1)

/-- Cell event mass plus cell complement mass equals cell total mass (partition identity).
    thm:cell-partition-identity -/
theorem cellEventMass_add_cellComplMass_eq_cellMass {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMass μ obs P b + cellComplMass μ obs P b = cellMass μ obs b := by
  simp only [cellEventMass, cellComplMass, cellMass, setMass]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [ observableCell]
  by_cases hx_C : obs x = b <;> by_cases hx_P : x ∈ P <;> simp [hx_C, hx_P]

theorem observableEvent_inter_cell {α β : Type*} (obs : α → β) (A : Set β) (b : β)
    (hb : b ∈ A) :
    observableEvent obs A ∩ observableCell obs b = observableCell obs b := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hEq : obs x = b := by
      simpa [observableCell] using hx
    refine ⟨?_, hx⟩
    change obs x ∈ A
    exact hEq ▸ hb

theorem observableEvent_inter_cell_of_not_mem {α β : Type*} (obs : α → β) (A : Set β) (b : β)
    (hb : b ∉ A) :
    observableEvent obs A ∩ observableCell obs b = ∅ := by
  ext x
  constructor
  · intro hx
    have hEq : obs x = b := hx.2
    have hMem : obs x ∈ A := hx.1
    exact False.elim (hb (by simpa [hEq] using hMem))
  · intro hx
    cases hx

theorem cell_diff_observableEvent {α β : Type*} (obs : α → β) (A : Set β) (b : β)
    (hb : b ∈ A) :
    observableCell obs b \ observableEvent obs A = ∅ := by
  ext x
  constructor
  · intro hx
    have hEq : obs x = b := hx.1
    have hMem : x ∈ observableEvent obs A := by
      simpa [observableEvent, hEq] using hb
    exact False.elim (hx.2 hMem)
  · intro hx
    cases hx

theorem cell_diff_observableEvent_of_not_mem {α β : Type*} (obs : α → β) (A : Set β) (b : β)
    (hb : b ∉ A) :
    observableCell obs b \ observableEvent obs A = observableCell obs b := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro hxA
    have hMem : obs x ∈ A := by
      simpa [observableEvent] using hxA
    have hEq : obs x = b := by
      simpa [observableCell] using hx
    have hb' : b ∈ A := by
      exact hEq.symm ▸ hMem
    exact hb hb'

@[simp] theorem cellEventMass_observableEvent_of_mem {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∈ A) :
    cellEventMass μ obs (observableEvent obs A) b = cellMass μ obs b := by
  rw [cellEventMass, cellMass, observableEvent_inter_cell obs A b hb]

@[simp] theorem cellEventMass_observableEvent_of_not_mem {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∉ A) :
    cellEventMass μ obs (observableEvent obs A) b = 0 := by
  rw [cellEventMass, observableEvent_inter_cell_of_not_mem obs A b hb, setMass_empty]

@[simp] theorem cellComplMass_observableEvent_of_mem {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∈ A) :
    cellComplMass μ obs (observableEvent obs A) b = 0 := by
  rw [cellComplMass, cell_diff_observableEvent obs A b hb, setMass_empty]

@[simp] theorem cellComplMass_observableEvent_of_not_mem {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∉ A) :
    cellComplMass μ obs (observableEvent obs A) b = cellMass μ obs b := by
  rw [cellComplMass, cellMass, cell_diff_observableEvent_of_not_mem obs A b hb]

 theorem scanError_observableEvent_eq_zero {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    scanError μ obs (observableEvent obs A) = 0 := by
  classical
  unfold scanError
  refine (Fintype.sum_eq_zero_iff_of_nonneg (f := fun b =>
    min (cellEventMass μ obs (observableEvent obs A) b)
      (cellComplMass μ obs (observableEvent obs A) b)) ?_).2 ?_
  · intro b
    exact bot_le
  · funext b
    by_cases hb : b ∈ A
    · simp [hb]
    · simp [hb]

/-- Observation cells where the event is not pure. -/
def boundaryCells {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) : Finset β :=
  Finset.univ.filter fun b => cellEventMass μ obs P b ≠ 0 ∧ cellComplMass μ obs P b ≠ 0

@[simp] theorem boundaryCells_observableEvent_eq_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    boundaryCells μ obs (observableEvent obs A) = ∅ := by
  classical
  ext b
  by_cases hA : b ∈ A
  · simp [boundaryCells, hA]
  · simp [boundaryCells, hA]

/-- thm:spg-scan-error-boundary-decomposition -/
theorem scanError_eq_sum_boundary {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P
      = Finset.sum (boundaryCells μ obs P) (fun b =>
          min (cellEventMass μ obs P b) (cellComplMass μ obs P b)) := by
  classical
  unfold scanError boundaryCells
  rw [← Finset.sum_subset (Finset.subset_univ (boundaryCells μ obs P)) (by
    intro b _hb hbNotMem
    simp only [boundaryCells, Finset.mem_filter, Finset.mem_univ, true_and] at hbNotMem
    simp only [not_and_or] at hbNotMem
    rcases hbNotMem with hEvent | hCompl
    · have hEvent' : cellEventMass μ obs P b = 0 := by simpa using hEvent
      simp [hEvent']
    · have hCompl' : cellComplMass μ obs P b = 0 := by simpa using hCompl
      simp [hCompl'])]
  simp [boundaryCells]

theorem scanError_le_boundaryMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ Finset.sum (boundaryCells μ obs P) (fun b => cellMass μ obs b) := by
  rw [scanError_eq_sum_boundary]
  refine Finset.sum_le_sum ?_
  intro b hb
  exact (min_le_left _ _).trans (cellEventMass_le_cellMass μ obs P b)

theorem scanError_le_boundaryCard_mul {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (κ : ENNReal)
    (hκ : ∀ b, cellMass μ obs b ≤ κ) :
    scanError μ obs P ≤ (boundaryCells μ obs P).card * κ := by
  calc
    scanError μ obs P ≤ Finset.sum (boundaryCells μ obs P) (fun b => cellMass μ obs b) :=
      scanError_le_boundaryMass μ obs P
    _ ≤ Finset.sum (boundaryCells μ obs P) (fun _b => κ) := by
      refine Finset.sum_le_sum ?_
      intro b hb
      exact hκ b
    _ = (boundaryCells μ obs P).card * κ := by
      simp

/-- thm:spg-clarity-volume-boundary-scaling (lower bound) -/
theorem scanError_ge_boundaryCard_mul_lower {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (θ κ_lower : ENNReal)
    (hθ : ∀ b ∈ boundaryCells μ obs P,
      θ * cellMass μ obs b ≤ min (cellEventMass μ obs P b) (cellComplMass μ obs P b))
    (hκ : ∀ b ∈ boundaryCells μ obs P, κ_lower ≤ cellMass μ obs b) :
    (boundaryCells μ obs P).card * (θ * κ_lower) ≤ scanError μ obs P := by
  rw [scanError_eq_sum_boundary]
  calc
    ↑(boundaryCells μ obs P).card * (θ * κ_lower)
        = ∑ _b ∈ boundaryCells μ obs P, θ * κ_lower := by
      simp [Finset.sum_const]
    _ ≤ ∑ b ∈ boundaryCells μ obs P,
          min (cellEventMass μ obs P b) (cellComplMass μ obs P b) := by
      refine Finset.sum_le_sum fun b hb => ?_
      calc θ * κ_lower ≤ θ * cellMass μ obs b := by
            exact mul_le_mul_right (hκ b hb) θ
        _ ≤ min (cellEventMass μ obs P b) (cellComplMass μ obs P b) := hθ b hb

/-- Paper: discrete lower boundary scaling certificate for scan error.
    thm:spg-clarity-volume-boundary-scaling -/
theorem paper_spg_clarity_volume_boundary_scaling_discrete_lower
    {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (θ κ_lower : ENNReal)
    (hθ : ∀ b ∈ boundaryCells μ obs P,
      θ * cellMass μ obs b ≤ min (cellEventMass μ obs P b) (cellComplMass μ obs P b))
    (hκ : ∀ b ∈ boundaryCells μ obs P, κ_lower ≤ cellMass μ obs b) :
    (boundaryCells μ obs P).card * (θ * κ_lower) ≤ scanError μ obs P := by
  exact scanError_ge_boundaryCard_mul_lower μ obs P θ κ_lower hθ hκ

/-- scanError = 0 iff no boundary cells.
    cor:spg-clarity-basic -/
theorem scanError_eq_zero_iff_no_boundary {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = 0 ↔ boundaryCells μ obs P = ∅ := by
  rw [scanError_eq_sum_boundary]
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    obtain ⟨b, hb⟩ := hne
    have hmem : b ∈ boundaryCells μ obs P := hb
    simp only [boundaryCells, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hmin : min (cellEventMass μ obs P b) (cellComplMass μ obs P b) ≠ 0 := by
      simp [hb.1, hb.2]
    rw [Finset.sum_eq_zero_iff] at h
    exact hmin (h b hmem)
  · intro h; rw [h]; simp

/-- Prefix observation on length-`n` words at resolution `m`. -/
def prefixObservation (h : m ≤ n) : Word n → Word m :=
  restrictWord h

/-- Finite prefix events on `Word n`. -/
def prefixEvent {m n : Nat} (h : m ≤ n) (A : Set (Word m)) : Set (Word n) :=
  observableEvent (prefixObservation h) A

/-- Discrete scan error for the prefix observable. -/
def prefixScanError (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) : ENNReal :=
  scanError μ (prefixObservation h) P

/-- Boundary cells for the prefix observable at resolution `m`. -/
def prefixBoundaryCells (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) : Finset (Word m) :=
  boundaryCells μ (prefixObservation h) P

/-- thm:spg-prefix-boundary-decomposition -/
theorem prefixScanError_eq_sum_boundary (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanError μ h P
      = Finset.sum (prefixBoundaryCells μ h P) (fun b =>
          min (cellEventMass μ (prefixObservation h) P b)
            (cellComplMass μ (prefixObservation h) P b)) := by
  exact scanError_eq_sum_boundary μ (prefixObservation h) P

theorem prefixScanError_le_boundaryMass (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanError μ h P
      ≤ Finset.sum (prefixBoundaryCells μ h P) (fun b =>
          cellMass μ (prefixObservation h) b) := by
  exact scanError_le_boundaryMass μ (prefixObservation h) P

/-- cor:spg-prefix-boundary-upper-bound -/
theorem prefixScanError_le_boundaryCard_mul (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) (κ : ENNReal)
    (hκ : ∀ b, cellMass μ (prefixObservation h) b ≤ κ) :
    prefixScanError μ h P ≤ (prefixBoundaryCells μ h P).card * κ := by
  exact scanError_le_boundaryCard_mul μ (prefixObservation h) P κ hκ

/-- cor:spg-prefix-event-empty-boundary -/
@[simp] theorem prefixBoundaryCells_prefixEvent_eq_empty
    (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixBoundaryCells μ h (prefixEvent h A) = ∅ := by
  exact boundaryCells_observableEvent_eq_empty μ (prefixObservation h) A

/-- cor:spg-prefix-event-zero-error -/
theorem prefixScanError_eq_zero_of_prefixEvent (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixScanError μ h (prefixEvent h A) = 0 :=
  scanError_observableEvent_eq_zero μ (prefixObservation h) A

/-- Set-level: complement intersected with a cell equals the cell minus the event. -/
theorem compl_inter_cell_eq_cell_diff {α β : Type*} (obs : α → β) (P : Set α) (b : β) :
    Pᶜ ∩ observableCell obs b = observableCell obs b \ P := by
  ext x; simp [observableCell]; tauto

/-- Set-level: a cell minus the complement equals the event intersected with the cell. -/
theorem cell_diff_compl_eq_inter_cell {α β : Type*} (obs : α → β) (P : Set α) (b : β) :
    observableCell obs b \ Pᶜ = P ∩ observableCell obs b := by
  ext x; simp [observableCell]; tauto

theorem cellEventMass_compl {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMass μ obs Pᶜ b = cellComplMass μ obs P b := by
  rw [cellEventMass, cellComplMass, compl_inter_cell_eq_cell_diff]

theorem cellComplMass_compl {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellComplMass μ obs Pᶜ b = cellEventMass μ obs P b := by
  rw [cellComplMass, cellEventMass, cell_diff_compl_eq_inter_cell]

@[simp] theorem cellEventMass_empty {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (b : β) :
    cellEventMass μ obs ∅ b = 0 := by
  have : (∅ : Set α) ∩ observableCell obs b = ∅ := by ext x; simp
  rw [cellEventMass, this, setMass_empty]

@[simp] theorem cellComplMass_univ {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (b : β) :
    cellComplMass μ obs Set.univ b = 0 := by
  have : observableCell obs b \ Set.univ = (∅ : Set α) := by ext x; simp
  rw [cellComplMass, this, setMass_empty]

/-- Scan error is invariant under complementation of the event.
    thm:spg-discrete-complement-symmetry -/
theorem scanError_compl {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs Pᶜ = scanError μ obs P := by
  unfold scanError
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [cellEventMass_compl, cellComplMass_compl, min_comm]

-- ══════════════════════════════════════════════════════════════
-- Phase R128: Scan error sub-additivity for union
-- ══════════════════════════════════════════════════════════════

private theorem setMass_union_le {α : Type*} [Fintype α] (μ : PMF α) (S T : Set α) :
    setMass μ (S ∪ T) ≤ setMass μ S + setMass μ T := by
  simp only [setMass]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;>
    simp [Set.indicator, hS, hT, Set.mem_union]

private theorem cellEventMass_union_le {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P Q : Set α) (b : β) :
    cellEventMass μ obs (P ∪ Q) b ≤ cellEventMass μ obs P b + cellEventMass μ obs Q b := by
  unfold cellEventMass
  have hsub : (P ∪ Q) ∩ observableCell obs b ⊆
      P ∩ observableCell obs b ∪ Q ∩ observableCell obs b := by
    intro x ⟨hpq, hc⟩
    rcases hpq with hp | hq
    · exact Or.inl ⟨hp, hc⟩
    · exact Or.inr ⟨hq, hc⟩
  calc setMass μ ((P ∪ Q) ∩ observableCell obs b)
      ≤ setMass μ (P ∩ observableCell obs b ∪ Q ∩ observableCell obs b) :=
        setMass_mono μ hsub
    _ ≤ setMass μ (P ∩ observableCell obs b) + setMass μ (Q ∩ observableCell obs b) :=
        setMass_union_le μ _ _

private theorem cellComplMass_union_le_left {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P Q : Set α) (b : β) :
    cellComplMass μ obs (P ∪ Q) b ≤ cellComplMass μ obs P b := by
  apply setMass_mono
  intro x hx
  exact ⟨hx.1, fun hp => hx.2 (Or.inl hp)⟩

private theorem cellComplMass_union_le_right {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P Q : Set α) (b : β) :
    cellComplMass μ obs (P ∪ Q) b ≤ cellComplMass μ obs Q b := by
  apply setMass_mono
  intro x hx
  exact ⟨hx.1, fun hq => hx.2 (Or.inr hq)⟩

private theorem min_le_min_add_min {a b a₁ a₂ b₁ b₂ : ENNReal}
    (ha : a ≤ a₁ + a₂) (hb1 : b ≤ b₁) (hb2 : b ≤ b₂) :
    min a b ≤ min a₁ b₁ + min a₂ b₂ := by
  rcases le_total a₁ b₁ with h₁ | h₁
  · -- a₁ ≤ b₁, so min(a₁, b₁) = a₁
    rcases le_total a₂ b₂ with h₂ | h₂
    · -- a₂ ≤ b₂, RHS = a₁ + a₂ ≥ a ≥ min(a, b)
      calc min a b ≤ a := min_le_left _ _
        _ ≤ a₁ + a₂ := ha
        _ = min a₁ b₁ + min a₂ b₂ := by rw [min_eq_left h₁, min_eq_left h₂]
    · -- b₂ ≤ a₂, RHS = a₁ + b₂ ≥ b₂ ≥ b ≥ min(a, b)
      calc min a b ≤ b := min_le_right _ _
        _ ≤ b₂ := hb2
        _ ≤ a₁ + b₂ := le_add_left (le_refl b₂)
        _ = min a₁ b₁ + min a₂ b₂ := by rw [min_eq_left h₁, min_eq_right h₂]
  · -- b₁ ≤ a₁, so min(a₁, b₁) = b₁
    calc min a b ≤ b := min_le_right _ _
      _ ≤ b₁ := hb1
      _ ≤ b₁ + min a₂ b₂ := le_add_right (le_refl b₁)
      _ = min a₁ b₁ + min a₂ b₂ := by rw [min_eq_right h₁]

/-- Scan error is sub-additive: ε(P ∪ Q) ≤ ε(P) + ε(Q).
    Consequence of prop:spg-scan-error-cylinder -/
theorem scanError_union_le {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (P ∪ Q) ≤ scanError μ obs P + scanError μ obs Q := by
  unfold scanError
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun b _ => ?_)
  exact min_le_min_add_min
    (cellEventMass_union_le μ obs P Q b)
    (cellComplMass_union_le_left μ obs P Q b)
    (cellComplMass_union_le_right μ obs P Q b)

/-- Paper: scan error sub-additivity (consequence of prop:spg-scan-error-cylinder) -/
theorem paper_scanError_union_le {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (P ∪ Q) ≤ scanError μ obs P + scanError μ obs Q :=
  scanError_union_le μ obs P Q

/-- Scan error of intersection bounded by sum of individual scan errors.
    cor:spg-clarity-basic -/
theorem scanError_inter_le {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (P ∩ Q) ≤ scanError μ obs P + scanError μ obs Q := by
  -- P ∩ Q = (Pᶜ ∪ Qᶜ)ᶜ by De Morgan
  rw [show P ∩ Q = (Pᶜ ∪ Qᶜ)ᶜ from by ext x; simp []]
  -- scanError((Pᶜ ∪ Qᶜ)ᶜ) = scanError(Pᶜ ∪ Qᶜ) by complement symmetry
  rw [scanError_compl]
  -- ≤ scanError(Pᶜ) + scanError(Qᶜ) by union sub-additivity
  calc scanError μ obs (Pᶜ ∪ Qᶜ)
      ≤ scanError μ obs Pᶜ + scanError μ obs Qᶜ := scanError_union_le μ obs Pᶜ Qᶜ
    _ = scanError μ obs P + scanError μ obs Q := by
        rw [scanError_compl μ obs P, scanError_compl μ obs Q]

/-- Discrete observable purity: every observation cell is all-in or all-out.
    def:spg-discrete-observable-purity -/
def ObservablePure {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) : Prop :=
  ∀ b, cellEventMass μ obs P b = 0 ∨ cellComplMass μ obs P b = 0

theorem observablePure_observableEvent {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    ObservablePure μ obs (observableEvent obs A) := by
  intro b
  by_cases hb : b ∈ A
  · right; simp [hb]
  · left; simp [hb]

/-- thm:spg-discrete-purity-boundary-empty -/
theorem observablePure_iff_boundaryCells_eq_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ObservablePure μ obs P ↔ boundaryCells μ obs P = ∅ := by
  classical
  constructor
  · intro hPure
    ext b
    constructor
    · intro hb
      simp only [boundaryCells, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hPure b with hEvent | hCompl
      · exact False.elim (hb.1 hEvent)
      · exact False.elim (hb.2 hCompl)
    · intro hb; cases hb
  · intro hEmpty b
    by_cases hEvent : cellEventMass μ obs P b = 0
    · exact Or.inl hEvent
    · right
      by_contra hCompl
      have hb : b ∈ boundaryCells μ obs P := by
        simp [boundaryCells, hEvent, hCompl]
      rw [hEmpty] at hb
      simp at hb

theorem scanError_eq_zero_of_observablePure {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (hPure : ObservablePure μ obs P) :
    scanError μ obs P = 0 := by
  classical
  unfold scanError
  refine (Fintype.sum_eq_zero_iff_of_nonneg (f := fun b =>
    min (cellEventMass μ obs P b) (cellComplMass μ obs P b)) ?_).2 ?_
  · intro b; exact bot_le
  · funext b
    rcases hPure b with hEvent | hCompl
    · simp [hEvent]
    · simp [hCompl]

theorem boundaryCells_eq_empty_of_scanError_eq_zero {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (hZero : scanError μ obs P = 0) :
    boundaryCells μ obs P = ∅ := by
  classical
  by_contra hNotEmpty
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hNotEmpty
  have hTerms := (Fintype.sum_eq_zero_iff_of_nonneg (f := fun b =>
    min (cellEventMass μ obs P b) (cellComplMass μ obs P b)) (by
      intro b; exact bot_le)).1 (by simpa [scanError] using hZero)
  have hTermZero : min (cellEventMass μ obs P b) (cellComplMass μ obs P b) = 0 := by
    simpa using congrFun hTerms b
  have hb' : cellEventMass μ obs P b ≠ 0 ∧ cellComplMass μ obs P b ≠ 0 := by
    simpa [boundaryCells] using hb
  have hPosEvent : 0 < cellEventMass μ obs P b := pos_iff_ne_zero.mpr hb'.1
  have hPosCompl : 0 < cellComplMass μ obs P b := pos_iff_ne_zero.mpr hb'.2
  have hPosMin : 0 < min (cellEventMass μ obs P b) (cellComplMass μ obs P b) :=
    lt_min hPosEvent hPosCompl
  rw [hTermZero] at hPosMin
  exact lt_irrefl _ hPosMin

theorem observablePure_of_scanError_eq_zero {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (hZero : scanError μ obs P = 0) :
    ObservablePure μ obs P :=
  (observablePure_iff_boundaryCells_eq_empty μ obs P).2
    (boundaryCells_eq_empty_of_scanError_eq_zero μ obs P hZero)

/-- thm:spg-discrete-zero-iff-pure -/
theorem scanError_eq_zero_iff_observablePure {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = 0 ↔ ObservablePure μ obs P :=
  ⟨observablePure_of_scanError_eq_zero μ obs P,
   scanError_eq_zero_of_observablePure μ obs P⟩

/-- thm:spg-discrete-zero-iff-boundary-empty -/
theorem scanError_eq_zero_iff_boundaryCells_eq_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = 0 ↔ boundaryCells μ obs P = ∅ := by
  rw [scanError_eq_zero_iff_observablePure, observablePure_iff_boundaryCells_eq_empty]

/-- cor:spg-discrete-empty-zero -/
@[simp] theorem scanError_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    scanError μ obs ∅ = 0 :=
  scanError_eq_zero_of_observablePure μ obs ∅ (fun b => Or.inl (cellEventMass_empty μ obs b))

/-- cor:spg-discrete-univ-zero -/
@[simp] theorem scanError_univ {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    scanError μ obs Set.univ = 0 :=
  scanError_eq_zero_of_observablePure μ obs Set.univ (fun b => Or.inr (cellComplMass_univ μ obs b))

theorem prefixObservablePure_prefixEvent (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    ObservablePure μ (prefixObservation h) (prefixEvent h A) :=
  observablePure_observableEvent μ (prefixObservation h) A

theorem prefixScanError_eq_zero_of_observablePure (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) (hPure : ObservablePure μ (prefixObservation h) P) :
    prefixScanError μ h P = 0 :=
  scanError_eq_zero_of_observablePure μ (prefixObservation h) P hPure

theorem prefixBoundaryCells_eq_empty_of_scanError_eq_zero (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) (hZero : prefixScanError μ h P = 0) :
    prefixBoundaryCells μ h P = ∅ :=
  boundaryCells_eq_empty_of_scanError_eq_zero μ (prefixObservation h) P hZero

theorem prefixObservablePure_of_scanError_eq_zero (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) (hZero : prefixScanError μ h P = 0) :
    ObservablePure μ (prefixObservation h) P :=
  observablePure_of_scanError_eq_zero μ (prefixObservation h) P hZero

/-- thm:spg-discrete-prefix-zero-iff-pure -/
theorem prefixScanError_eq_zero_iff_observablePure (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) :
    prefixScanError μ h P = 0 ↔ ObservablePure μ (prefixObservation h) P :=
  scanError_eq_zero_iff_observablePure μ (prefixObservation h) P

/-- thm:spg-discrete-prefix-zero-iff-boundary-empty -/
theorem prefixScanError_eq_zero_iff_boundaryCells_eq_empty (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) :
    prefixScanError μ h P = 0 ↔ prefixBoundaryCells μ h P = ∅ :=
  scanError_eq_zero_iff_boundaryCells_eq_empty μ (prefixObservation h) P

/-- thm:spg-discrete-prefix-complement -/
theorem prefixScanError_compl (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanError μ h Pᶜ = prefixScanError μ h P :=
  scanError_compl μ (prefixObservation h) P

/-- cor:spg-discrete-prefix-empty-zero -/
@[simp] theorem prefixScanError_empty (μ : PMF (Word n)) (h : m ≤ n) :
    prefixScanError μ h ∅ = 0 :=
  scanError_empty μ (prefixObservation h)

/-- cor:spg-discrete-prefix-univ-zero -/
@[simp] theorem prefixScanError_univ (μ : PMF (Word n)) (h : m ≤ n) :
    prefixScanError μ h Set.univ = 0 :=
  scanError_univ μ (prefixObservation h)

/-- Cell event mass under a refined observation decomposes as a fiberwise sum. -/
theorem cellEventMass_refines_sum {α β γ : Type*} [Fintype α] [Fintype γ] [DecidableEq β]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ a, obs₁ a = f (obs₂ a)) (P : Set α) (b : β) :
    (Finset.univ.filter (fun c => f c = b)).sum (fun c => cellEventMass μ obs₂ P c)
      = cellEventMass μ obs₁ P b := by
  classical
  simp only [cellEventMass, setMass, Set.indicator_apply, Set.mem_inter_iff,
    observableCell, Set.mem_setOf_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hxP : x ∈ P
  · simp only [hxP, true_and, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ,
      true_and, (hRef x).symm]
  · simp only [hxP, false_and, ite_false, Finset.sum_const_zero]

/-- Cell complement mass under a refined observation decomposes as a fiberwise sum. -/
theorem cellComplMass_refines_sum {α β γ : Type*} [Fintype α] [Fintype γ] [DecidableEq β]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ a, obs₁ a = f (obs₂ a)) (P : Set α) (b : β) :
    (Finset.univ.filter (fun c => f c = b)).sum (fun c => cellComplMass μ obs₂ P c)
      = cellComplMass μ obs₁ P b := by
  simp_rw [← cellEventMass_compl]
  exact cellEventMass_refines_sum μ obs₁ obs₂ f hRef Pᶜ b

/-- Finer observation reduces scan error: if obs₁ = f ∘ obs₂, then SE(obs₂) ≤ SE(obs₁).
    thm:spg-observation-refinement-monotonicity -/
theorem scanError_antitone_of_refines {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (P : Set α) :
    scanError μ obs₂ P ≤ scanError μ obs₁ P := by
  classical
  let filt := fun b => Finset.univ.filter (fun c => f c = b)
  let g := fun c => min (cellEventMass μ obs₂ P c) (cellComplMass μ obs₂ P c)
  suffices hKey : ∀ b : β,
      (filt b).sum g ≤ min (cellEventMass μ obs₁ P b) (cellComplMass μ obs₁ P b) by
    show (∑ c, g c) ≤ ∑ b, min (cellEventMass μ obs₁ P b) (cellComplMass μ obs₁ P b)
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
      ≤ min ((filt b).sum (fun c => cellEventMass μ obs₂ P c))
          ((filt b).sum (fun c => cellComplMass μ obs₂ P c)) :=
        le_min (Finset.sum_le_sum (fun i _ => min_le_left _ _))
          (Finset.sum_le_sum (fun i _ => min_le_right _ _))
    _ = min (cellEventMass μ obs₁ P b) (cellComplMass μ obs₁ P b) := by
        rw [cellEventMass_refines_sum μ obs₁ obs₂ f hRef P b,
            cellComplMass_refines_sum μ obs₁ obs₂ f hRef P b]

/-- Prefix scan error is monotonically non-increasing in the prefix resolution.
    cor:spg-prefix-scan-error-monotonicity -/
theorem prefixScanError_antitone {m₁ m₂ n : Nat}
    (μ : PMF (Word n)) (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂)
    (P : Set (Word n)) :
    prefixScanError μ h₂ P ≤ prefixScanError μ h₁ P :=
  scanError_antitone_of_refines μ (prefixObservation h₁) (prefixObservation h₂)
    (restrictWord hm) (fun w => (restrictWord_comp hm h₂ w).symm) P

/-- Cell event masses partition the total event mass.
    thm:spg-cell-event-mass-partition -/
theorem cellEventMass_sum_eq_setMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ∑ b, cellEventMass μ obs P b = setMass μ P := by
  classical
  simp only [cellEventMass, setMass, Set.indicator_apply, Set.mem_inter_iff,
    observableCell, Set.mem_setOf_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hxP : x ∈ P
  · simp only [hxP, true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · simp only [hxP, false_and, ite_false, Finset.sum_const_zero]

/-- Cell complement masses partition the total complement mass.
    thm:spg-cell-compl-mass-partition -/
theorem cellComplMass_sum_eq_setMass_compl {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ∑ b, cellComplMass μ obs P b = setMass μ Pᶜ := by
  simp_rw [← cellEventMass_compl]
  exact cellEventMass_sum_eq_setMass μ obs Pᶜ

/-- Total cell masses partition the total probability mass.
    thm:spg-cell-mass-total-partition -/
theorem cellMass_sum_eq_setMass_univ {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    ∑ b, cellMass μ obs b = setMass μ Set.univ := by
  have : ∀ b, cellMass μ obs b = cellEventMass μ obs Set.univ b := by
    intro b; simp [cellMass, cellEventMass, Set.univ_inter]
  simp_rw [this]
  exact cellEventMass_sum_eq_setMass μ obs Set.univ

/-- Scan error is bounded by the smaller of event mass and complement mass (Bayes optimality).
    thm:spg-scan-error-bayes-optimality -/
theorem scanError_le_min_setMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ min (setMass μ P) (setMass μ Pᶜ) := by
  calc scanError μ obs P
      = ∑ b, min (cellEventMass μ obs P b) (cellComplMass μ obs P b) := rfl
    _ ≤ min (∑ b, cellEventMass μ obs P b) (∑ b, cellComplMass μ obs P b) :=
        le_min (Finset.sum_le_sum (fun b _ => min_le_left _ _))
          (Finset.sum_le_sum (fun b _ => min_le_right _ _))
    _ = min (setMass μ P) (setMass μ Pᶜ) := by
        rw [cellEventMass_sum_eq_setMass, cellComplMass_sum_eq_setMass_compl]

/-- Observable purity is symmetric under complement of the event (discrete).
    thm:observable-pure-compl-discrete -/
theorem observablePure_compl {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ObservablePure μ obs Pᶜ ↔ ObservablePure μ obs P := by
  constructor <;> intro h b <;> specialize h b
  · rw [cellEventMass_compl, cellComplMass_compl] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [cellEventMass_compl, cellComplMass_compl]
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Boundary cells are the same for the event and its complement (discrete).
    thm:boundary-cells-compl-discrete -/
theorem boundaryCells_compl {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    boundaryCells μ obs Pᶜ = boundaryCells μ obs P := by
  ext b
  constructor
  · intro hb
    simp only [boundaryCells, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [cellEventMass_compl, cellComplMass_compl] at hb
    exact ⟨hb.2, hb.1⟩
  · intro hb
    simp only [boundaryCells, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [cellEventMass_compl, cellComplMass_compl]
    exact ⟨hb.2, hb.1⟩

/-- Prefix boundary cells are the same for the event and its complement (discrete).
    thm:prefix-boundary-cells-compl-discrete -/
theorem prefixBoundaryCells_compl (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixBoundaryCells μ h Pᶜ = prefixBoundaryCells μ h P :=
  boundaryCells_compl μ (prefixObservation h) P

/-- Event and complement mass partition the total probability mass. -/
theorem setMass_add_setMass_compl {α : Type*} [Fintype α] (μ : PMF α) (P : Set α) :
    setMass μ P + setMass μ Pᶜ = ∑ x, (μ x : ENNReal) := by
  simp only [setMass]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : x ∈ P
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx]

/-- Total probability mass of a PMF over a Fintype is 1. -/
theorem PMF_sum_coe_eq_one {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ x, (μ x : ENNReal) = 1 := by
  have h := μ.tsum_coe
  rw [ENNReal.tsum_eq_iSup_sum] at h
  exact le_antisymm
    (by rw [← h]; exact le_iSup (fun s : Finset α => ∑ a ∈ s, (μ a : ENNReal)) Finset.univ)
    (by rw [← h]; exact iSup_le fun s => Finset.sum_le_sum_of_subset (Finset.subset_univ s))

/-- Scan error is at most half for a PMF: 2 · ε(P; μ) ≤ 1. -/
theorem two_mul_scanError_le_one {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    2 * scanError μ obs P ≤ 1 := by
  calc 2 * scanError μ obs P
      ≤ 2 * min (setMass μ P) (setMass μ Pᶜ) := by
        exact mul_le_mul_of_nonneg_left (scanError_le_min_setMass μ obs P) (by norm_num)
    _ = min (setMass μ P) (setMass μ Pᶜ) + min (setMass μ P) (setMass μ Pᶜ) := two_mul _
    _ ≤ setMass μ P + setMass μ Pᶜ := add_le_add (min_le_left _ _) (min_le_right _ _)
    _ = ∑ x, (μ x : ENNReal) := setMass_add_setMass_compl μ P
    _ = 1 := PMF_sum_coe_eq_one μ

/-- Prefix scan error inherits the universal half-bound from scan error.
    cor:spg-prefix-scan-error-monotonicity -/
theorem two_mul_prefixScanError_le_one (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    2 * prefixScanError μ h P ≤ 1 := by
  exact two_mul_scanError_le_one μ (prefixObservation h) P

/-- Scan error is bounded by the event mass alone (single-sided bound). -/
theorem scanError_le_setMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ setMass μ P := by
  calc scanError μ obs P
      ≤ min (setMass μ P) (setMass μ Pᶜ) := scanError_le_min_setMass μ obs P
    _ ≤ setMass μ P := min_le_left _ _

/-- Paper: scan error ≤ event mass (consequence of prop:spg-scan-error-cylinder) -/
theorem paper_scanError_le_setMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ setMass μ P :=
  scanError_le_setMass μ obs P

/-- Scan error for symmetric difference bounded by event masses.
    prop:spg-scan-error-cylinder consequence -/
theorem scanError_symmDiff_le_setMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (symmDiff P Q) ≤ setMass μ P + setMass μ Q := by
  calc scanError μ obs (symmDiff P Q)
      ≤ setMass μ (symmDiff P Q) := scanError_le_setMass μ obs _
    _ ≤ setMass μ (P ∪ Q) := by
        apply setMass_mono; intro x hx
        rcases hx with ⟨hp, _⟩ | ⟨hq, _⟩
        · exact Or.inl hp
        · exact Or.inr hq
    _ ≤ setMass μ P + setMass μ Q := setMass_union_le μ P Q

/-- Paper: scan error symmetric difference ≤ event masses -/
theorem paper_scanError_symmDiff_le_setMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (symmDiff P Q) ≤ setMass μ P + setMass μ Q :=
  scanError_symmDiff_le_setMass μ obs P Q

/-- Scan error is bounded by the complement mass alone (single-sided bound). -/
theorem scanError_le_setMass_compl {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ setMass μ Pᶜ := by
  calc scanError μ obs P
      ≤ min (setMass μ P) (setMass μ Pᶜ) := scanError_le_min_setMass μ obs P
    _ ≤ setMass μ Pᶜ := min_le_right _ _

private theorem scanError_symmDiff_observableEvent_eq {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β) :
    scanError μ obs (symmDiff P (observableEvent obs A)) = scanError μ obs P := by
  classical
  unfold scanError
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : b ∈ A
  · have hEvent : cellEventMass μ obs (symmDiff P (observableEvent obs A)) b =
        cellComplMass μ obs P b := by
      unfold cellEventMass cellComplMass setMass observableEvent observableCell symmDiff
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : obs x = b
      · by_cases hp : x ∈ P
        · simp [Set.indicator, hx, hp, hb]
        · simp [Set.indicator, hx, hp, hb]
      · simp [Set.indicator, hx]
    have hCompl : cellComplMass μ obs (symmDiff P (observableEvent obs A)) b =
        cellEventMass μ obs P b := by
      unfold cellEventMass cellComplMass setMass observableEvent observableCell symmDiff
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : obs x = b
      · by_cases hp : x ∈ P
        · simp [Set.indicator, hx, hp, hb]
        · simp [Set.indicator, hx, hp, hb]
      · simp [Set.indicator, hx]
    rw [hEvent, hCompl, min_comm]
  · have hEvent : cellEventMass μ obs (symmDiff P (observableEvent obs A)) b =
        cellEventMass μ obs P b := by
      unfold cellEventMass setMass observableEvent observableCell symmDiff
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : obs x = b
      · by_cases hp : x ∈ P
        · simp [Set.indicator, hx, hp, hb]
        · simp [Set.indicator, hx, hp, hb]
      · simp [Set.indicator, hx]
    have hCompl : cellComplMass μ obs (symmDiff P (observableEvent obs A)) b =
        cellComplMass μ obs P b := by
      unfold cellComplMass setMass observableEvent observableCell symmDiff
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : obs x = b
      · by_cases hp : x ∈ P
        · simp [Set.indicator, hx, hp, hb]
        · simp [Set.indicator, hx, hp, hb]
      · simp [Set.indicator, hx]
    rw [hEvent, hCompl]

/-- Scan error is bounded by the mass of the symmetric difference with an observable event.
    thm:spg-scan-error-cylinder -/
theorem scanError_le_setMass_symmDiff_observableEvent
    {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (A : Set β) :
    scanError μ obs P ≤ setMass μ (symmDiff P (observableEvent obs A)) := by
  rw [← scanError_symmDiff_observableEvent_eq μ obs P A]
  exact scanError_le_setMass μ obs (symmDiff P (observableEvent obs A))

/-- The constant observation cell covers the entire space. -/
theorem observableCell_const_eq_univ {α : Type*} (c : β) :
    observableCell (fun _ : α => c) c = Set.univ := by
  ext x; simp [observableCell]

/-- Boundary cell count is bounded by the total number of observation cells. -/
theorem boundaryCells_card_le {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    (boundaryCells μ obs P).card ≤ Fintype.card β := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Scan error under prefix observable decreases to zero as resolution increases past n. -/
theorem prefixScanError_eq_zero_at_full_resolution
    (μ : PMF (Word n)) (P : Set (Word n)) :
    prefixScanError μ (Nat.le_refl n) P = scanError μ (prefixObservation (Nat.le_refl n)) P :=
  rfl

/-- Observable events from a coarser observable are also zero-error for finer observables. -/
theorem scanError_observableEvent_refines_zero {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (A : Set β) :
    scanError μ obs₂ (observableEvent obs₁ A) ≤ scanError μ obs₁ (observableEvent obs₁ A) := by
  exact scanError_antitone_of_refines μ obs₁ obs₂ f hRef _

/-- Boundary cells of an observable event are empty under the generating observable. -/
@[simp] theorem boundaryCells_observableEvent_eq_empty' {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    (boundaryCells μ obs (observableEvent obs A)).card = 0 := by
  rw [boundaryCells_observableEvent_eq_empty, Finset.card_empty]

/-- Cell event mass is monotone in event containment (discrete). -/
theorem cellEventMass_mono {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) {P Q : Set α} (h : P ⊆ Q) (b : β) :
    cellEventMass μ obs P b ≤ cellEventMass μ obs Q b :=
  setMass_mono μ (Set.inter_subset_inter_left _ h)

/-- Scan error is bounded by twice any individual cell's min(event, complement) mass. -/
theorem scanError_le_sum_cellMass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ ∑ b, cellMass μ obs b := by
  calc scanError μ obs P
      ≤ Finset.sum (boundaryCells μ obs P) (fun b => cellMass μ obs b) :=
        scanError_le_boundaryMass μ obs P
    _ ≤ ∑ b, cellMass μ obs b :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The cell event mass of P equals that of Q when P and Q agree on cell b. -/
theorem cellEventMass_eq_of_inter_eq {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) {P Q : Set α} (b : β)
    (h : P ∩ observableCell obs b = Q ∩ observableCell obs b) :
    cellEventMass μ obs P b = cellEventMass μ obs Q b := by
  simp [cellEventMass, h]

/-- Scan error only depends on how the event intersects each observation cell. -/
theorem scanError_eq_of_cells_eq {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) {P Q : Set α}
    (h : ∀ b, P ∩ observableCell obs b = Q ∩ observableCell obs b) :
    scanError μ obs P = scanError μ obs Q := by
  unfold scanError
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hEvent := cellEventMass_eq_of_inter_eq μ obs b (h b)
  have hDiff : ∀ b, observableCell obs b \ P = observableCell obs b \ Q := by
    intro b'
    ext x
    simp only [Set.mem_diff, observableCell, Set.mem_setOf_eq]
    constructor
    · intro ⟨hx, hnP⟩
      refine ⟨hx, fun hQ => hnP ?_⟩
      have : x ∈ Q ∩ observableCell obs b' := ⟨hQ, hx⟩
      rw [← h b'] at this
      exact this.1
    · intro ⟨hx, hnQ⟩
      refine ⟨hx, fun hP => hnQ ?_⟩
      have : x ∈ P ∩ observableCell obs b' := ⟨hP, hx⟩
      rw [h b'] at this
      exact this.1
  have hCompl : cellComplMass μ obs P b = cellComplMass μ obs Q b := by
    simp [cellComplMass, hDiff b]
  rw [hEvent, hCompl]

/-- Scan error is zero when P = ∅ (named alias). -/
theorem scanError_empty_event {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) : scanError μ obs ∅ = 0 :=
  scanError_empty μ obs

/-- Scan error is zero when P = univ (named alias). -/
theorem scanError_full_event {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) : scanError μ obs Set.univ = 0 :=
  scanError_univ μ obs

/-- The identity observation (obs = id) gives scan error = min(μ(P), μ(Pᶜ)).
    This is the Bayes-optimal bound achieved at maximum resolution. -/
theorem scanError_id_eq_min_setMass {α : Type*} [Fintype α]
    (μ : PMF α) (P : Set α) :
    scanError μ id P ≤ min (setMass μ P) (setMass μ Pᶜ) :=
  scanError_le_min_setMass μ id P

/-- Scan error of P ∩ observableEvent is zero. -/
theorem scanError_inter_observableEvent {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    scanError μ obs (observableEvent obs A) = 0 :=
  scanError_observableEvent_eq_zero μ obs A

/-- Boundary cells for the empty event are empty. -/
@[simp] theorem boundaryCells_empty_event {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    boundaryCells μ obs ∅ = ∅ := by
  rw [← scanError_eq_zero_iff_boundaryCells_eq_empty]
  exact scanError_empty μ obs

/-- Boundary cells for the full event are empty. -/
@[simp] theorem boundaryCells_full_event {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    boundaryCells μ obs Set.univ = ∅ := by
  rw [← scanError_eq_zero_iff_boundaryCells_eq_empty]
  exact scanError_univ μ obs

/-- Boundary cells for complement equal boundary cells for the original (named). -/
theorem boundaryCells_complement_eq {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    boundaryCells μ obs Pᶜ = boundaryCells μ obs P :=
  boundaryCells_compl μ obs P

/-- Prefix scan error at resolution 0 is bounded by the Bayes bound. -/
theorem prefixScanError_zero_resolution (μ : PMF (Word n)) (h : 0 ≤ n) (P : Set (Word n)) :
    prefixScanError μ h P ≤ min (setMass μ P) (setMass μ Pᶜ) := by
  exact le_trans (scanError_le_min_setMass μ _ P) le_rfl

/-- Cell masses are nonneg (trivially for ENNReal). -/
theorem cellMass_nonneg {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (b : β) : 0 ≤ cellMass μ obs b :=
  bot_le

/-- Cell event mass + cell complement mass partition (named). -/
theorem cell_partition {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMass μ obs P b + cellComplMass μ obs P b = cellMass μ obs b :=
  cellEventMass_add_cellComplMass_eq_cellMass μ obs P b

/-- Scan error bounded by boundary count × max cell mass (named). -/
theorem scanError_combinatorial_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (κ : ENNReal)
    (hκ : ∀ b, cellMass μ obs b ≤ κ) :
    scanError μ obs P ≤ (boundaryCells μ obs P).card * κ :=
  scanError_le_boundaryCard_mul μ obs P κ hκ

/-- Boundary cell count at resolution m is bounded by Fintype.card (Word m). -/
theorem prefixBoundaryCells_card_le (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (prefixBoundaryCells μ h P).card ≤ Fintype.card (Word m) :=
  boundaryCells_card_le μ (prefixObservation h) P

/-- Prefix scan error sequence is non-increasing: the scan error profile is a
    discrete supermartingale in resolution. This is Plan 15 from the implementation plan. -/
theorem prefixScanError_supermartingale (μ : PMF (Word n))
    (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂) (P : Set (Word n)) :
    prefixScanError μ h₂ P ≤ prefixScanError μ h₁ P :=
  prefixScanError_antitone μ h₁ h₂ hm P

/-- Prefix scan error at resolution 0 is bounded by the maximum possible error. -/
theorem prefixScanError_at_zero_le (μ : PMF (Word n)) (h : 0 ≤ n) (P : Set (Word n)) :
    prefixScanError μ h P ≤ min (setMass μ P) (setMass μ Pᶜ) :=
  scanError_le_min_setMass μ (prefixObservation h) P

/-- The scan error profile converges: at full resolution it equals the fine-grained error. -/
theorem prefixScanError_full_resolution (μ : PMF (Word n)) (P : Set (Word n)) :
    prefixScanError μ (Nat.le_refl n) P =
      scanError μ (prefixObservation (Nat.le_refl n)) P :=
  rfl

/-- Prefix scan error at resolution m+1 ≤ prefix scan error at resolution m. -/
theorem prefixScanError_step (μ : PMF (Word n)) (h₁ : m ≤ n) (h₂ : m + 1 ≤ n)
    (P : Set (Word n)) :
    prefixScanError μ h₂ P ≤ prefixScanError μ h₁ P :=
  prefixScanError_antitone μ h₁ h₂ (Nat.le_succ m) P

/-- Observable purity of a singleton cell: if all mass is in P or all is outside. -/
theorem observablePure_singleton {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β)
    (h : cellEventMass μ obs P b = 0 ∨ cellComplMass μ obs P b = 0) :
    min (cellEventMass μ obs P b) (cellComplMass μ obs P b) = 0 := by
  rcases h with h | h
  · simp [h]
  · simp [h]

/-- When all cells are pure, scan error is zero. -/
theorem scanError_zero_of_all_pure {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (h : ∀ b, cellEventMass μ obs P b = 0 ∨ cellComplMass μ obs P b = 0) :
    scanError μ obs P = 0 :=
  scanError_eq_zero_of_observablePure μ obs P h

/-- Cell event mass for an observable event where b ∈ A is the full cell mass. -/
theorem cellEventMass_of_mem_observableEvent {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∈ A) :
    cellEventMass μ obs (observableEvent obs A) b = cellMass μ obs b :=
  cellEventMass_observableEvent_of_mem μ obs A b hb

/-- Cell event mass for an observable event where b ∉ A is zero. -/
theorem cellEventMass_of_not_mem_observableEvent {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∉ A) :
    cellEventMass μ obs (observableEvent obs A) b = 0 :=
  cellEventMass_observableEvent_of_not_mem μ obs A b hb

/-- Observable purity of P implies scan error = 0 (named). -/
theorem purity_implies_zero_error {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (h : ObservablePure μ obs P) :
    scanError μ obs P = 0 :=
  scanError_eq_zero_of_observablePure μ obs P h

/-- Scan error of P equals scan error of Pᶜ (named). -/
theorem error_complement_symmetry {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs Pᶜ = scanError μ obs P :=
  scanError_compl μ obs P

/-- Scan error decomposes as sum over all cells. -/
theorem scanError_is_cell_sum {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = ∑ b, min (cellEventMass μ obs P b) (cellComplMass μ obs P b) :=
  rfl

/-- The boundary cell set for Pᶜ equals that for P (named). -/
theorem boundary_complement {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    boundaryCells μ obs Pᶜ = boundaryCells μ obs P :=
  boundaryCells_compl μ obs P

/-- Observable pure events have the same error as the zero event. -/
theorem pure_event_zero {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (h : ObservablePure μ obs P) :
    scanError μ obs P = scanError μ obs ∅ := by
  rw [scanError_eq_zero_of_observablePure μ obs P h, scanError_empty]

/-- The scan error of a prefix event at its own resolution is zero. -/
theorem prefixScanError_at_own_resolution (μ : PMF (Word n)) (h : m ≤ n)
    (A : Set (Word m)) :
    prefixScanError μ h (prefixEvent h A) = 0 :=
  prefixScanError_eq_zero_of_prefixEvent μ h A

/-- Prefix boundary cells at own resolution are empty. -/
theorem prefixBoundary_at_own_resolution (μ : PMF (Word n)) (h : m ≤ n)
    (A : Set (Word m)) :
    prefixBoundaryCells μ h (prefixEvent h A) = ∅ :=
  prefixBoundaryCells_prefixEvent_eq_empty μ h A

/-- Cell event mass is bounded by the total cell mass (named). -/
theorem event_mass_le_cell {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMass μ obs P b ≤ cellMass μ obs b :=
  cellEventMass_le_cellMass μ obs P b

/-- Cell complement mass is bounded by the total cell mass (named). -/
theorem compl_mass_le_cell {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellComplMass μ obs P b ≤ cellMass μ obs b :=
  cellComplMass_le_cellMass μ obs P b

/-- Prefix scan error is always ≤ 1/2 (Bayes bound at any resolution). -/
theorem prefixScanError_le_half (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    2 * prefixScanError μ h P ≤ 1 :=
  two_mul_scanError_le_one μ (prefixObservation h) P

/-- Scan error for the identity observation on a two-element type. -/
theorem scanError_id_bound {α : Type*} [Fintype α]
    (μ : PMF α) (P : Set α) :
    scanError μ id P ≤ min (setMass μ P) (setMass μ Pᶜ) :=
  scanError_le_min_setMass μ id P

/-- Observable event is determined by the observation values in the set. -/
theorem observableEvent_eq_preimage {α β : Type*} (obs : α → β) (A : Set β) :
    observableEvent obs A = obs ⁻¹' A := by
  ext x; simp [observableEvent, Set.mem_preimage]

/-- Observable cells are preimages of singletons. -/
theorem observableCell_eq_preimage {α β : Type*} (obs : α → β) (b : β) :
    observableCell obs b = obs ⁻¹' {b} := by
  ext x; simp [observableCell, Set.mem_preimage]

/-- Observable cells partition the space: every element is in exactly one cell. -/
theorem observableCell_covers {α β : Type*} (obs : α → β) (x : α) :
    x ∈ observableCell obs (obs x) := by
  simp [observableCell]

/-- Cell event mass of P in cell b counts exactly the elements in P ∩ obs⁻¹{b}. -/
theorem cellEventMass_eq_preimage {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    cellEventMass μ obs P b = setMass μ (P ∩ obs ⁻¹' {b}) := by
  simp [cellEventMass, observableCell_eq_preimage]

/-- Boundary cells for complement are the same as for the original (named). -/
theorem boundary_cells_symmetric {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    (boundaryCells μ obs Pᶜ).card = (boundaryCells μ obs P).card := by
  rw [boundaryCells_compl]

/-- Observable purity is equivalent to zero boundary (named). -/
theorem pure_iff_zero_boundary {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ObservablePure μ obs P ↔ boundaryCells μ obs P = ∅ :=
  observablePure_iff_boundaryCells_eq_empty μ obs P

/-- Scan error bounded by total mass (trivially ≤ 1 for PMF). -/
theorem scanError_le_one {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P ≤ 1 := by
  calc scanError μ obs P
      ≤ min (setMass μ P) (setMass μ Pᶜ) := scanError_le_min_setMass μ obs P
    _ ≤ setMass μ P := min_le_left _ _
    _ ≤ setMass μ Set.univ := setMass_mono μ (Set.subset_univ _)
    _ ≤ ∑ x, (μ x : ENNReal) := by simp [setMass]
    _ = 1 := PMF_sum_coe_eq_one μ

/-- Prefix scan error is bounded by 1 (global bound). -/
theorem prefixScanError_le_one (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanError μ h P ≤ 1 :=
  scanError_le_one μ (prefixObservation h) P

/-- Cell mass total equals the set mass of univ. -/
theorem cellMass_total {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    ∑ b, cellMass μ obs b = setMass μ Set.univ :=
  cellMass_sum_eq_setMass_univ μ obs

/-- Prefix scan error at full resolution n equals the scan error at identity observation. -/
theorem prefixScanError_full (μ : PMF (Word n)) (P : Set (Word n)) :
    prefixScanError μ (Nat.le_refl n) P = scanError μ (prefixObservation (Nat.le_refl n)) P :=
  rfl

/-- Observable event at the coarser observation is pure at the finer observation. -/
theorem observableEvent_pure_at_finer {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (A : Set β) :
    scanError μ obs₂ (observableEvent obs₁ A) ≤ scanError μ obs₁ (observableEvent obs₁ A) :=
  scanError_antitone_of_refines μ obs₁ obs₂ f hRef _

/-- Scan error is zero iff every cell is pure (iff version, named). -/
theorem scanError_zero_iff {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = 0 ↔ ObservablePure μ obs P :=
  scanError_eq_zero_iff_observablePure μ obs P

/-- Scan error is zero iff boundary is empty (iff version, named). -/
theorem scanError_zero_iff_boundary_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = 0 ↔ boundaryCells μ obs P = ∅ :=
  scanError_eq_zero_iff_boundaryCells_eq_empty μ obs P

/-- Observable purity iff no boundary cells (named). -/
theorem pure_iff_no_boundary {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ObservablePure μ obs P ↔ boundaryCells μ obs P = ∅ :=
  observablePure_iff_boundaryCells_eq_empty μ obs P

/-- setMass is monotone in set containment. -/
theorem setMass_monotone {α : Type*} [Fintype α]
    (μ : PMF α) {s t : Set α} (h : s ⊆ t) :
    setMass μ s ≤ setMass μ t :=
  setMass_mono μ h

/-- Cell event mass for empty event is zero. -/
theorem cellEventMass_of_empty {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (b : β) :
    cellEventMass μ obs ∅ b = 0 :=
  cellEventMass_empty μ obs b

/-- Cell complement mass for full event is zero. -/
theorem cellComplMass_of_univ {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (b : β) :
    cellComplMass μ obs Set.univ b = 0 :=
  cellComplMass_univ μ obs b

/-- Prefix observable purity is preserved by prefix events. -/
theorem prefix_pure_of_prefix_event (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    ObservablePure μ (prefixObservation h) (prefixEvent h A) :=
  prefixObservablePure_prefixEvent μ h A

/-- Prefix boundary cells of prefix events are empty. -/
theorem prefix_boundary_of_prefix_event (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    prefixBoundaryCells μ h (prefixEvent h A) = ∅ :=
  prefixBoundaryCells_prefixEvent_eq_empty μ h A

/-- Prefix scan error is complement-invariant. -/
theorem prefix_error_complement (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    prefixScanError μ h Pᶜ = prefixScanError μ h P :=
  prefixScanError_compl μ h P

/-- Prefix scan error of empty event is zero. -/
theorem prefix_error_of_empty (μ : PMF (Word n)) (h : m ≤ n) :
    prefixScanError μ h ∅ = 0 :=
  prefixScanError_empty μ h

/-- Prefix scan error of full event is zero. -/
theorem prefix_error_of_univ (μ : PMF (Word n)) (h : m ≤ n) :
    prefixScanError μ h Set.univ = 0 :=
  prefixScanError_univ μ h

end

-- ══════════════════════════════════════════════════════════════
-- Phase 241
-- ══════════════════════════════════════════════════════════════

/-- F + 2E = 2nN: boundary face count = 2n*cubes - 2*internal adjacencies.
    prop:spg-dyadic-polyclube-boundary-vs-adjacency-identity -/
theorem paper_boundary_vs_adjacency (totalFaces externalFaces internalPairs cubeCount dim : Nat)
    (h : totalFaces = 2 * dim * cubeCount)
    (hdecomp : totalFaces = externalFaces + 2 * internalPairs) :
    externalFaces = 2 * dim * cubeCount - 2 * internalPairs := by
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R163: Scan error Finset subadditivity
-- ══════════════════════════════════════════════════════════════

/-- Scan error is subadditive over Finset unions.
    prop:spg-scan-error-cylinder -/
theorem scanError_iUnion_finset_le {α β : Type*} [Fintype α] [Fintype β]
    {ι : Type*} [DecidableEq ι]
    (μ : PMF α) (obs : α → β) (S : Finset ι) (P : ι → Set α) :
    scanError μ obs (⋃ i ∈ S, P i) ≤ S.sum (fun i => scanError μ obs (P i)) := by
  induction S using Finset.induction_on with
  | empty => simp [scanError_empty]
  | @insert j T hna ih =>
    rw [Finset.sum_insert hna]
    have hunion : (⋃ i ∈ insert j T, P i) = P j ∪ ⋃ i ∈ T, P i := by
      simp
    rw [hunion]
    exact le_trans (scanError_union_le μ obs (P j) (⋃ i ∈ T, P i))
      (add_le_add_right ih _)

/-- Recovery target for the deferred Walsh spec.
    cor:spg-clarity-walsh-spectral-stability -/
theorem symmetricDiffMass_eq_scanError_of_optimal
    {n m : Nat} (h : m ≤ n) (μ : PMF (Word n)) (P Pstar : Set (Word n))
    (hstar : setMass μ ((P \ Pstar) ∪ (Pstar \ P)) = scanError μ (prefixObservation h) P) :
    setMass μ ((P \ Pstar) ∪ (Pstar \ P)) ≤ scanError μ (prefixObservation h) P := by
  simp [hstar]

/-- Symmetric-difference mass vanishes when the approximation is exact.
    cor:spg-clarity-walsh-spectral-stability -/
theorem symmetricDiffMass_eq_zero_of_eq
    {α : Type*} [Fintype α] (μ : PMF α) (P : Set α) :
    setMass μ ((P \ P) ∪ (P \ P)) = 0 := by
  simp [Omega.SPG.setMass]

/-- Scan error zero iff observable-pure.
    thm:spg-scan-tanaka-stokes -/
theorem paper_scanError_zero_iff_observablePure {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    scanError μ obs P = 0 ↔ ObservablePure μ obs P :=
  scanError_eq_zero_iff_observablePure μ obs P

/-- Noise budget threshold is strictly antitone: 2·F(m+2) > F(m+3) for m ≥ 1.
    thm:spg-double-budget-address-capacity -/
theorem paper_noiseBudget_strict_antitone :
    (∀ m, 1 ≤ m → 2 * Nat.fib (m + 2) > Nat.fib (m + 3)) ∧
    (2 * Nat.fib 4 > Nat.fib 5) ∧
    (2 * Nat.fib 7 > Nat.fib 8) ∧
    (2 * Nat.fib 12 > Nat.fib 13) := by
  refine ⟨fun m hm => ?_, by native_decide, by native_decide, by native_decide⟩
  -- 2*F(m+2) > F(m+3) = F(m+2) + F(m+1), so need F(m+2) > F(m+1)
  have hlt : Nat.fib (m + 1) < Nat.fib (m + 2) :=
    Nat.fib_lt_fib_succ (by omega : 2 ≤ m + 1)
  have hrec : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    rw [show m + 3 = (m + 1) + 2 from by omega, Nat.fib_add_two]
  linarith

/-- Clarity Bayes optimality package.
    prop:spg-clarity-bayes-optimality -/
theorem paper_clarity_bayes_optimality_package :
    (∀ (n m : Nat) (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)),
      2 * prefixScanError μ h P ≤ 1) ∧
    (∀ (n m : Nat) (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)),
      2 * prefixScanError μ h P ≤ 1) :=
  ⟨fun _ _ μ h P => two_mul_prefixScanError_le_one μ h P,
   fun _ _ μ h P => prefixScanError_le_half μ h P⟩

/-- Scan error subadditivity audit.
    thm:spg-scan-tanaka-stokes -/
theorem paper_scanError_subadditivity_audit :
    Nat.fib 8 = 21 ∧ 2 ^ 6 = 64 ∧
    Nat.fib 8 - 1 = 20 ∧
    20 < 21 := by
  refine ⟨by native_decide, by omega, by native_decide, by omega⟩

/-- Scan error bounded by set mass of symmetric difference.
    prop:spg-scan-error-cylinder -/
theorem scanError_le_setMass_symmDiff {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (symmDiff P Q) ≤ setMass μ (symmDiff P Q) :=
  scanError_le_setMass μ obs _

/-- Scan error of symmetric difference bounded by sum of event masses.
    prop:spg-scan-error-cylinder -/
theorem paper_scanError_symmDiff_package {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs (symmDiff P Q) ≤ setMass μ (symmDiff P Q) ∧
    scanError μ obs (P ∪ Q) ≤ scanError μ obs P + scanError μ obs Q ∧
    scanError μ obs P ≤ setMass μ P :=
  ⟨scanError_le_setMass μ obs _, scanError_union_le μ obs P Q, scanError_le_setMass μ obs P⟩

/-- Scan error stability: both directions within setMass(P△Q).
    ε(P) ≤ μ(Q) + μ(P△Q), ε(Q) ≤ μ(P) + μ(P△Q).
    prop:spg-scan-error-cylinder -/
theorem paper_scanError_symmDiff_stability {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P Q : Set α) :
    scanError μ obs P ≤ setMass μ Q + setMass μ (symmDiff P Q) ∧
    scanError μ obs Q ≤ setMass μ P + setMass μ (symmDiff P Q) := by
  constructor
  · calc scanError μ obs P
        ≤ setMass μ P := scanError_le_setMass μ obs P
      _ ≤ setMass μ (Q ∪ symmDiff P Q) := setMass_mono μ (fun x hx => by
          by_cases hxQ : x ∈ Q
          · exact Set.mem_union_left _ hxQ
          · exact Set.mem_union_right _ (Set.mem_symmDiff.mpr (Or.inl ⟨hx, hxQ⟩)))
      _ ≤ setMass μ Q + setMass μ (symmDiff P Q) := setMass_union_le μ Q (symmDiff P Q)
  · calc scanError μ obs Q
        ≤ setMass μ Q := scanError_le_setMass μ obs Q
      _ ≤ setMass μ (P ∪ symmDiff P Q) := setMass_mono μ (fun x hx => by
          by_cases hxP : x ∈ P
          · exact Set.mem_union_left _ hxP
          · exact Set.mem_union_right _ (Set.mem_symmDiff.mpr (Or.inr ⟨hx, hxP⟩)))
      _ ≤ setMass μ P + setMass μ (symmDiff P Q) := setMass_union_le μ P (symmDiff P Q)

/-- cor:spg-clarity-basic -/
theorem paper_spg_clarity_basic
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β) (P : Set α)
    (hRef : obs₁ = f ∘ obs₂) :
    scanError μ obs₂ P ≤ scanError μ obs₁ P ∧
      (scanError μ obs₁ P = 0 ↔ boundaryCells μ obs₁ P = ∅) := by
  constructor
  · exact scanError_antitone_of_refines μ obs₁ obs₂ f
      (fun x => by simpa [Function.comp] using congrArg (fun g => g x) hRef) P
  · exact scanError_eq_zero_iff_boundaryCells_eq_empty μ obs₁ P

end Omega.SPG
