import Omega.Frontier.ConditionalSPG
import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.FiberRing

namespace Omega.Frontier

noncomputable section


/-! ### Paper Section 6: Complete Abelian Group Structure -/

/-- X_m forms an abelian group: additive inverse exists. -/
theorem stableAdd_inverse (x : X m) :
    X.stableAdd x (X.stableNeg x) = X.stableZero :=
  X.stableAdd_stableNeg x

/-- Negation is a right inverse. -/
theorem stableNeg_right_inverse (x : X m) :
    X.stableAdd (X.stableNeg x) x = X.stableZero :=
  X.stableNeg_stableAdd x

/-- Negation of zero is zero. -/
theorem stableNeg_of_zero : X.stableNeg (X.stableZero (m := m)) = X.stableZero :=
  X.stableNeg_zero

/-- Stable subtraction cancels addition: (x + y) - y = x. -/
theorem stableSub_cancel (x y : X m) :
    X.stableSub (X.stableAdd x y) y = x :=
  X.stableSub_stableAdd_cancel x y

/-- Two stable words with equal values are identical. -/
theorem stableWord_eq_of_value_eq {x y : X m} (h : stableValue x = stableValue y) : x = y :=
  X.eq_of_stableValue_eq h

/-- Fold is the identity on the underlying word of a stable element. -/
theorem fold_val_identity (x : X m) : (Fold x.1).1 = x.1 :=
  X.Fold_val_stable x

/-! ### Paper SPG Section: fromWordSet Algebra -/

/-- fromWordSet distributes over intersection. -/
theorem fromWordSet_inter (A B : Set (Word m)) :
    SPG.fromWordSet (A ∩ B) = SPG.fromWordSet A ∩ SPG.fromWordSet B :=
  SPG.fromWordSet_inter A B

/-- fromWordSet distributes over union. -/
theorem fromWordSet_union (A B : Set (Word m)) :
    SPG.fromWordSet (A ∪ B) = SPG.fromWordSet A ∪ SPG.fromWordSet B :=
  SPG.fromWordSet_union A B

/-- Prefix-determined sets at depth 0 are trivial (empty or universal). -/
theorem prefixDetermined_zero_trivial (s : Set SPG.OmegaInfinity) :
    SPG.PrefixDetermined s 0 ↔ s = ∅ ∨ s = Set.univ :=
  SPG.prefixDetermined_zero_iff s

/-! ### Paper Fold Section: Rewrite Irreducibility Equivalence -/

/-- A digit configuration is irreducible iff it is stable (binary, no adjacent positives). -/
theorem rewrite_irreducible_iff_stable {a : Rewrite.DigitCfg} :
    Rewrite.Irreducible a ↔ Rewrite.StableCfg a :=
  Rewrite.irreducible_iff_stableCfg

/-! ### Paper Section 6: Negation Value -/

/-- The value of the additive inverse. -/
theorem stableNeg_value (x : X m) :
    stableValue (X.stableNeg x) = (Nat.fib (m + 2) - stableValue x) % Nat.fib (m + 2) :=
  X.stableValue_stableNeg x

/-! ### Paper Section 6: Ring Structure Characterization -/

/-- stableValue characterizes equality of stable words. -/
theorem stableValue_characterizes_equality (x y : X m) :
    x = y ↔ stableValue x = stableValue y :=
  X.stableValue_eq_iff x y

/-- Right distributivity of multiplication over addition. -/
theorem stableMul_distributes_right (x y z : X m) :
    X.stableMul (X.stableAdd y z) x = X.stableAdd (X.stableMul y x) (X.stableMul z x) :=
  X.stableMul_stableAdd_right x y z

/-! ### Paper SPG Section: Scan Error Bounds -/

/-- Scan error ≤ sum of cell event measures. -/
theorem scanError_measure_le_event_sum [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P ≤ ∑ b, SPG.cellEventMeasure μ obs P b :=
  SPG.scanErrorMeasure_le_cellEventSum μ obs P

/-- Scan error ≤ sum of cell complement measures. -/
theorem scanError_measure_le_compl_sum [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P ≤ ∑ b, SPG.cellComplMeasure μ obs P b :=
  SPG.scanErrorMeasure_le_cellComplSum μ obs P

/-- Observable purity implies zero boundary count (measure). -/
theorem pure_implies_zero_boundary [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hPure : SPG.ObservablePureMeasure μ obs P) :
    SPG.boundaryCylinderCount μ obs P = 0 :=
  SPG.boundaryCylinderCount_zero_of_pure μ obs P hPure

/-! ### Paper Theorem 4.1/6.1: Ring Surjectivity & Fiber Disjointness -/

/-- Every value in {0,...,F_{m+2}-1} is realized by some stable word. -/
theorem stableValue_surjective (n : Nat) (hn : n < Nat.fib (m + 2)) :
    ∃ x : X m, stableValue x = n :=
  X.stableValue_ring_surjective n hn

/-- Distinct stable words have disjoint Fold fibers. -/
theorem fold_fibers_disjoint {x y : X m} (hne : x ≠ y) :
    Disjoint (X.fiber x) (X.fiber y) :=
  X.fiber_disjoint hne

/-! ### Paper SPG Section: Scan Error Total Mass Bound -/

/-- Scan error is bounded by the total cell mass (discrete). -/
theorem scanError_le_total_cell_mass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P ≤ ∑ b, SPG.cellMass μ obs b :=
  SPG.scanError_le_sum_cellMass μ obs P

/-! ### Paper SPG Section: Clopen & Topological Structure -/

/-- Cylinder sets are clopen. -/
theorem cylinder_is_clopen (w : Word m) : IsClopen (SPG.cylinderWord w) :=
  SPG.isClopen_cylinderWord w

/-- Clopen intersection of fromWordSets. -/
theorem fromWordSet_inter_clopen (A B : Set (Word m)) :
    IsClopen (SPG.fromWordSet A ∩ SPG.fromWordSet B) :=
  SPG.isClopen_fromWordSet_inter A B

/-! ### Paper Defect Section: Defect Self-Cancellation -/

/-- Local defect xor'd with itself vanishes. -/
theorem localDefect_self_cancel (η : Word (m + 1)) :
    xorWord (localDefect η) (localDefect η) = zeroWord m :=
  localDefect_xor_localDefect η

/-- Global defect xor'd with itself vanishes. -/
theorem globalDefect_self_cancel (h : m ≤ n) (ω : Word n) :
    xorWord (globalDefect h ω) (globalDefect h ω) = zeroWord m :=
  globalDefect_xor_self h ω

/-! ### Paper SPG Section: Scan Error Cell-Locality -/

/-- Scan error depends only on cell-level intersections (discrete). -/
theorem scanError_cell_local {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) {P Q : Set α}
    (h : ∀ b, P ∩ SPG.observableCell obs b = Q ∩ SPG.observableCell obs b) :
    SPG.scanError μ obs P = SPG.scanError μ obs Q :=
  SPG.scanError_eq_of_cells_eq μ obs h

/-! ### Paper SPG Section: Clopen Cylinder -/

/-- Individual cylinder sets are clopen in the product topology. -/
theorem cylinder_clopen (w : Word m) : IsClopen (SPG.cylinderWord w) :=
  SPG.isClopen_cylinderWord w

/-! ### Paper Section 6: Cancellation & Isomorphism Summary -/

/-- Left cancellation for stable addition. -/
theorem stableAdd_left_cancel_wrapper {x y z : X m}
    (h : X.stableAdd x y = X.stableAdd x z) : y = z :=
  X.stableAdd_left_cancel h

/-- Right cancellation for stable addition. -/
theorem stableAdd_right_cancel_wrapper {x y z : X m}
    (h : X.stableAdd y x = X.stableAdd z x) : y = z :=
  X.stableAdd_right_cancel h

/-- Subtraction followed by addition recovers the original: (x - y) + y = x. -/
theorem stableSub_then_add (x y : X m) :
    X.stableAdd (X.stableSub x y) y = x :=
  X.stableSub_add_cancel x y

/-- Self-subtraction gives zero. -/
theorem stableSub_self_eq_zero (x : X m) : X.stableSub x x = X.stableZero :=
  X.stableSub_self x

/-- stableValue is a complete ring isomorphism to ℤ/F_{m+2}ℤ
    (additive hom + multiplicative hom + injective + surjective). -/
theorem stableValue_ring_isomorphism (m : Nat) :
    (∀ x y : X m, stableValue (X.stableAdd x y) =
      (stableValue x + stableValue y) % Nat.fib (m + 2)) ∧
    (∀ x y : X m, stableValue (X.stableMul x y) =
      (stableValue x * stableValue y) % Nat.fib (m + 2)) ∧
    Function.Injective (stableValue (m := m)) ∧
    Set.range (stableValue (m := m)) = {n | n < Nat.fib (m + 2)} :=
  X.stableValue_isomorphism_summary m

/-! ### Paper Section 4: Concrete Cardinalities -/

/-- |X_1| = 2. -/
theorem card_stable_one : Fintype.card (X 1) = 2 := X.card_X_one
/-- |X_2| = 3. -/
theorem card_stable_two : Fintype.card (X 2) = 3 := X.card_X_two
/-- |X_3| = 5. -/
theorem card_stable_three : Fintype.card (X 3) = 5 := X.card_X_three
/-- |X_4| = 8. -/
theorem card_stable_four : Fintype.card (X 4) = 8 := X.card_X_four
/-- |X_5| = 13. -/
theorem card_stable_five : Fintype.card (X 5) = 13 := X.card_X_five

/-! ### Paper Section 4: Weight Structure -/

/-- Weight decomposes by last bit: false preserves, true adds F_{m+1}. -/
theorem weight_last_false {w : Word (m + 1)} (h : w ⟨m, Nat.lt_succ_self m⟩ = false) :
    weight w = weight (truncate w) :=
  weight_of_lastFalse h

/-- Weight is positive when the last bit is true. -/
theorem weight_positive_of_true {w : Word (m + 1)} (h : w ⟨m, Nat.lt_succ_self m⟩ = true) :
    0 < weight w :=
  weight_pos_of_bit_true h

/-! ### Paper Section 6: stableOne Value -/

/-- stableOne has value 1 for m ≥ 1 (multiplicative unit). -/
theorem stableOne_value (hm : 1 ≤ m) :
    stableValue (X.stableOne (m := m)) = 1 :=
  X.stableValue_stableOne_of_ge_one hm

/-! ### Paper SPG Section: Identity Observation Bound -/

/-- The identity observation achieves the Bayes-optimal bound. -/
theorem identity_observation_bayes {α : Type*} [Fintype α]
    (μ : PMF α) (P : Set α) :
    SPG.scanError μ id P ≤ min (SPG.setMass μ P) (SPG.setMass μ Pᶜ) :=
  SPG.scanError_id_eq_min_setMass μ P

/-- Scan error vanishes for the empty event. -/
theorem scanError_vanishes_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    SPG.scanError μ obs ∅ = 0 :=
  SPG.scanError_empty_event μ obs

/-- Scan error vanishes for the full event. -/
theorem scanError_vanishes_full {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    SPG.scanError μ obs Set.univ = 0 :=
  SPG.scanError_full_event μ obs

/-! ### Paper Section 6: Double Negation & Additional Cardinalities -/

/-- Double negation: -(-x) = x (involution property). -/
theorem stableNeg_involution (x : X m) : X.stableNeg (X.stableNeg x) = x :=
  X.stableNeg_neg_eq x

/-- |X_6| = 21. -/
theorem card_stable_six : Fintype.card (X 6) = 21 := X.card_X_six
/-- |X_7| = 34. -/
theorem card_stable_seven : Fintype.card (X 7) = 34 := X.card_X_seven

/-! ### Paper SPG: Boundary Cells for Trivial Events -/

/-- Empty boundary for empty event (discrete). -/
theorem boundaryCells_vanish_empty {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) : SPG.boundaryCells μ obs ∅ = ∅ :=
  SPG.boundaryCells_empty_event μ obs

/-- Empty boundary for full event (discrete). -/
theorem boundaryCells_vanish_full {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) : SPG.boundaryCells μ obs Set.univ = ∅ :=
  SPG.boundaryCells_full_event μ obs

/-- Observable purity for observable events (measure). -/
theorem observable_events_are_pure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.ObservablePureMeasure μ obs (SPG.observableEvent obs A) :=
  SPG.observablePureMeasure_of_observable μ obs A

/-! ### Paper Section 4: Higher Cardinalities & Group Laws -/

/-- |X_8| = 55. -/
theorem card_stable_eight : Fintype.card (X 8) = 55 := X.card_X_eight
/-- |X_9| = 89. -/
theorem card_stable_nine : Fintype.card (X 9) = 89 := X.card_X_nine
/-- |X_10| = 144. -/
theorem card_stable_ten : Fintype.card (X 10) = 144 := X.card_X_ten

/-- Negation-add cancellation: (-x) + (x + y) = y. -/
theorem neg_add_cancellation (x y : X m) :
    X.stableAdd (X.stableNeg x) (X.stableAdd x y) = y :=
  X.stableNeg_add_cancel x y

/-- Subtraction is addition with negation (definitional). -/
theorem sub_is_add_neg (x y : X m) :
    X.stableSub x y = X.stableAdd x (X.stableNeg y) :=
  X.stableSub_eq_add_neg x y

/-! ### Paper SPG: Cell Partition Named Variants -/

/-- Cell event + complement = total (discrete, named). -/
theorem cell_partition_discrete {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    SPG.cellEventMass μ obs P b + SPG.cellComplMass μ obs P b = SPG.cellMass μ obs b :=
  SPG.cell_partition μ obs P b

/-- Scan error is complement-invariant (discrete, named). -/
theorem scanError_complement_invariant {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs Pᶜ = SPG.scanError μ obs P :=
  SPG.scanError_compl μ obs P

/-- Scan error is complement-invariant (measure, named). -/
theorem scanError_measure_complement_invariant [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs Pᶜ = SPG.scanErrorMeasure μ obs P :=
  SPG.scanErrorMeasure_complement μ obs P

/-- Cell partition (measure, named). -/
theorem cell_partition_measure_named [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β)
    (hP : MeasurableSet P) :
    SPG.cellEventMeasure μ obs P b + SPG.cellComplMeasure μ obs P b = SPG.cellMeasure μ obs b :=
  SPG.cell_partition_measure μ obs P b hP

/-! ### Paper Section 6: Additional Group Laws -/

/-- (-x) + x = 0 (named). -/
theorem neg_plus_self_zero (x : X m) : X.stableAdd (X.stableNeg x) x = X.stableZero :=
  X.stableNeg_add_self x

/-- x + (-x) = 0 (named). -/
theorem self_plus_neg_zero (x : X m) : X.stableAdd x (X.stableNeg x) = X.stableZero :=
  X.stableAdd_self_neg x

/-! ### Paper Fold Section: Fold Properties Summary -/

/-- Fold is idempotent on raw words (named). -/
theorem fold_is_idempotent (w : Word m) : Fold (Fold w).1 = Fold w :=
  Fold_idempotent w

/-- Fold fixes stable words (named). -/
theorem fold_fixes_stable (x : X m) : Fold x.1 = x :=
  Fold_stable x

/-- Fold is surjective onto X_m (named). -/
theorem fold_is_surjective : Function.Surjective (Fold (m := m)) :=
  Fold_surjective m

/-- Every stable word is in its own fiber (named). -/
theorem stable_word_in_fiber (x : X m) : x.1 ∈ X.fiber x :=
  X.self_in_own_fiber x

/-! ### Paper Section 4: Fibonacci Cardinality Summary -/

/-- The Fibonacci cardinality sequence: |X_m| = F_{m+2}. -/
theorem fibonacci_cardinality (m : Nat) :
    Fintype.card (X m) = Nat.fib (m + 2) :=
  X.card_eq_fib m

/-- The Fibonacci recurrence for cardinalities: |X_{m+2}| = |X_{m+1}| + |X_m|. -/
theorem fibonacci_cardinality_recurrence (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) :=
  X.card_recurrence m

/-! ### Paper Inverse Limit: Summary -/

/-- The inverse limit equivalence: CompatibleFamily ≃ XInfinity. -/
noncomputable def inverse_limit_equiv : X.CompatibleFamily ≃ X.XInfinity :=
  X.inverseLimitEquiv

/-- The inverse limit left inverse. -/
theorem inverse_limit_left (F : X.CompatibleFamily) :
    X.toFamily (X.ofFamily F) = F :=
  X.toFamily_ofFamily F

/-- The inverse limit right inverse. -/
theorem inverse_limit_right (a : X.XInfinity) :
    X.ofFamily (X.toFamily a) = a :=
  X.ofFamily_toFamily a

/-! ### Paper SPG Section: Scan Error Summary -/

/-- Scan error vanishes for observable events (discrete, summary). -/
theorem scan_error_vanishes_observable {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    SPG.scanError μ obs (SPG.observableEvent obs A) = 0 :=
  SPG.scanError_observableEvent_eq_zero μ obs A

/-- Scan error vanishes for observable events (measure, summary). -/
theorem scan_error_measure_vanishes_observable [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.scanErrorMeasure μ obs (SPG.observableEvent obs A) = 0 :=
  SPG.scanErrorMeasure_observableEvent_eq_zero μ obs A

/-- Zero scan error ↔ observable purity (discrete, summary). -/
theorem scan_error_zero_iff_pure_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P = 0 ↔ SPG.ObservablePure μ obs P :=
  SPG.scanError_eq_zero_iff_observablePure μ obs P

/-- Zero scan error ↔ observable purity (measure, summary). -/
theorem scan_error_zero_iff_pure_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P = 0 ↔ SPG.ObservablePureMeasure μ obs P :=
  SPG.scanErrorMeasure_eq_zero_iff_observablePure μ obs P

/-! ### Paper Graph Section: Sofic Summary -/

/-- The stable language equals the golden-mean sofic language (summary). -/
theorem stable_language_is_sofic (m : Nat) :
    {w : Word m | No11 w} =
      {w : Word m | Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w} :=
  Omega.Graph.stableLanguage_eq_goldenMean m

/-! ### Paper Section 3: Observation Refinement & Half-Bound Summary -/

/-- Finer observation ⇒ lower scan error (discrete, summary). -/
theorem observation_refinement_reduces_error
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (P : Set α) :
    SPG.scanError μ obs₂ P ≤ SPG.scanError μ obs₁ P :=
  SPG.scanError_antitone_of_refines μ obs₁ obs₂ f hRef P

/-- Prefix scan error monotonically decreases with resolution (discrete, summary). -/
theorem prefix_resolution_decreases_error {m₁ m₂ n : Nat}
    (μ : PMF (Word n)) (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂)
    (P : Set (Word n)) :
    SPG.prefixScanError μ h₂ P ≤ SPG.prefixScanError μ h₁ P :=
  SPG.prefixScanError_antitone μ h₁ h₂ hm P

/-- Discrete Bayes half-bound: 2ε ≤ 1 for any PMF. -/
theorem discrete_bayes_half_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    2 * SPG.scanError μ obs P ≤ 1 :=
  SPG.two_mul_scanError_le_one μ obs P

/-- Prefix scan error complement invariance (discrete, summary). -/
theorem prefix_complement_invariance (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanError μ h Pᶜ = SPG.prefixScanError μ h P :=
  SPG.prefixScanError_compl μ h P

/-! ### Paper Section 6: Maximal Element & Non-triviality -/

/-- The negation of 1 gives the maximal element F_{m+2} - 1. -/
theorem neg_one_is_maximal (hm : 1 ≤ m) :
    stableValue (X.stableNeg (X.stableOne (m := m))) = Nat.fib (m + 2) - 1 :=
  X.stableValue_neg_one hm

/-- For m ≥ 1, the multiplicative identity is distinct from the additive identity. -/
theorem one_ne_zero_stable (hm : 1 ≤ m) : X.stableOne (m := m) ≠ X.stableZero :=
  X.stableOne_ne_stableZero hm

/-! ### Plan 4: Modular Projection Tower -/

/-- The modular projection from X_{m+1} to X_m via Fibonacci modulus. -/
noncomputable def modular_projection (x : X (m + 1)) : X m :=
  X.modularProject x

/-- Modular projection maps zero to zero. -/
theorem modular_projection_zero :
    X.modularProject (X.stableZero (m := m + 1)) = X.stableZero :=
  X.modularProject_zero

/-- Modular projection preserves addition when no carry occurs. -/
theorem modular_projection_add_no_carry (x y : X (m + 1))
    (h : stableValue x + stableValue y < Nat.fib (m + 3)) :
    X.modularProject (X.stableAdd x y) =
      X.stableAdd (X.modularProject x) (X.modularProject y) :=
  X.modularProject_add_no_carry x y h

/-! ### Plan 5: Fibonacci Divisibility -/

/-- Fibonacci divisibility: F_m | F_n when m | n. -/
theorem fibonacci_divisibility {m n : Nat} (h : m ∣ n) : Nat.fib m ∣ Nat.fib n :=
  Nat.fib_dvd m n h

/-- Fibonacci divisibility when successor indices divide. -/
theorem fib_divisibility {m n : Nat} (h : (m + 1) ∣ (n + 1)) :
    Nat.fib (m + 1) ∣ Nat.fib (n + 1) :=
  Nat.fib_dvd (m + 1) (n + 1) h

/-! ### Plan 7: Fiber Multiplicity Structure -/

/-- Total fiber multiplicity at resolution 0 is 1. -/
theorem fiber_total_at_zero : ∑ x : X 0, X.fiberMultiplicity x = 1 :=
  X.fiberMultiplicity_unique_at_zero

/-- Total fiber multiplicity at any resolution is 2^m. -/
theorem fiber_total_is_power (m : Nat) : ∑ x : X m, X.fiberMultiplicity x = 2 ^ m :=
  X.fiberMultiplicity_total m

/-! ### Plan 13: Scan Error Combinatorial Bounds -/

/-- Scan error bounded by boundary count × max cell mass. -/
theorem scanError_boundary_combinatorial {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (κ : ENNReal)
    (hκ : ∀ b, SPG.cellMass μ obs b ≤ κ) :
    SPG.scanError μ obs P ≤ (SPG.boundaryCells μ obs P).card * κ :=
  SPG.scanError_combinatorial_bound μ obs P κ hκ

/-- Prefix boundary cell count bounded by word space size. -/
theorem prefix_boundary_bounded (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (SPG.prefixBoundaryCells μ h P).card ≤ Fintype.card (Word m) :=
  SPG.prefixBoundaryCells_card_le μ h P

/-! ### Plan 6: Ring Isomorphism Certificate -/

/-- The ring isomorphism certificate for X_m ≅ ℤ/F_{m+2}ℤ. -/
noncomputable def ring_isomorphism_certificate (m : Nat) : X.RingIsomorphismCertificate m :=
  X.ringIsoCert m

/-! ### Plan 19: Transfer Matrix & Characteristic Polynomial -/

/-- The golden-mean graph transition count from each state. -/
theorem goldenMean_transition_false :
    Omega.Graph.goldenMeanTransitionCount false = 2 := rfl

/-- The golden-mean graph transition count from state true. -/
theorem goldenMean_transition_true :
    Omega.Graph.goldenMeanTransitionCount true = 1 := rfl

/-- The cardinality recurrence IS the characteristic polynomial relation:
    |X_{m+2}| = |X_{m+1}| + |X_m| corresponds to x² = x + 1 (eigenvalue φ). -/
theorem characteristic_polynomial_witness (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) :=
  Omega.Graph.goldenMean_characteristic_recurrence m

/-! ### Plan 1: Zeckendorf Uniqueness -/

/-- Zeckendorf uniqueness: same indices ⇒ same stable word. -/
theorem zeckendorf_uniqueness {x y : X m} (h : X.zeckIndices x = X.zeckIndices y) : x = y :=
  X.eq_of_zeckIndices_eq h

/-- Zeckendorf encoding is injective on stable words. -/
theorem zeckendorf_injective (m : Nat) : Function.Injective (X.zeckIndices (m := m)) :=
  X.zeckIndices_injective m

/-- Same Zeckendorf indices ⇒ same stable value. -/
theorem zeckendorf_determines_value {x y : X m}
    (h : X.zeckIndices x = X.zeckIndices y) : stableValue x = stableValue y :=
  X.stableValue_eq_of_zeckIndices_eq h

/-! ### Plan 8: Even/Odd Fiber Partition -/

/-- Even and odd value elements of X_m are disjoint. -/
theorem even_odd_elements_disjoint (m : Nat) :
    Disjoint (X.evenElements m) (X.oddElements m) :=
  X.even_odd_disjoint m

/-! ### Plan 24: Prefix σ-Algebra Chain -/

/-- The prefix algebra is monotone: determined at m ⇒ determined at n ≥ m. -/
theorem prefix_algebra_monotone {m n : Nat} (h : m ≤ n) :
    SPG.prefixAlgebra m ⊆ SPG.prefixAlgebra n :=
  SPG.prefixAlgebra_monotone h

/-- The prefix algebra at depth 0 is trivial: {∅, univ}. -/
theorem prefix_algebra_trivial_at_zero :
    SPG.prefixAlgebra 0 = {∅, Set.univ} :=
  SPG.prefixAlgebra_zero_trivial

/-- The prefix algebra is a Boolean algebra (complement closed). -/
theorem prefix_algebra_complement_closed {s : Set SPG.OmegaInfinity} {m : Nat}
    (hs : s ∈ SPG.prefixAlgebra m) : sᶜ ∈ SPG.prefixAlgebra m :=
  SPG.prefixAlgebra_compl_closed hs

/-- The prefix algebra is a Boolean algebra (intersection closed). -/
theorem prefix_algebra_inter_closed {s t : Set SPG.OmegaInfinity} {m : Nat}
    (hs : s ∈ SPG.prefixAlgebra m) (ht : t ∈ SPG.prefixAlgebra m) :
    s ∩ t ∈ SPG.prefixAlgebra m :=
  SPG.prefixAlgebra_inter_closed hs ht

/-- The prefix algebra is a Boolean algebra (union closed). -/
theorem prefix_algebra_union_closed {s t : Set SPG.OmegaInfinity} {m : Nat}
    (hs : s ∈ SPG.prefixAlgebra m) (ht : t ∈ SPG.prefixAlgebra m) :
    s ∪ t ∈ SPG.prefixAlgebra m :=
  SPG.prefixAlgebra_union_closed hs ht

/-! ### Plan 15: Scan Error Supermartingale -/

/-- Prefix scan error is a supermartingale in resolution. -/
theorem scan_error_supermartingale (μ : PMF (Word n))
    (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂) (P : Set (Word n)) :
    SPG.prefixScanError μ h₂ P ≤ SPG.prefixScanError μ h₁ P :=
  SPG.prefixScanError_supermartingale μ h₁ h₂ hm P

/-- One-step decrease: resolution m+1 error ≤ resolution m error. -/
theorem scan_error_step_decrease (μ : PMF (Word n))
    (h₁ : m ≤ n) (h₂ : m + 1 ≤ n) (P : Set (Word n)) :
    SPG.prefixScanError μ h₂ P ≤ SPG.prefixScanError μ h₁ P :=
  SPG.prefixScanError_step μ h₁ h₂ P

/-! ### Plan 22: Sofic Language Completeness -/

/-- Golden-mean accepts exactly No11 words (bidirectional). -/
theorem sofic_language_iff (w : Word m) :
    Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w ↔ No11 w :=
  Omega.Graph.goldenMean_language_complete m w

/-- Stable words are always accepted by the golden-mean presentation. -/
theorem stable_is_sofic (x : X m) :
    Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false x.1 :=
  Omega.Graph.stable_word_is_accepted x

/-! ### Plans 17/18: Measure-Level Scan Error Bounds -/

/-- Scan error ≤ event measure (with measurability). -/
theorem scanError_measure_le_event [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    SPG.scanErrorMeasure μ obs P ≤ μ P :=
  SPG.scanErrorMeasure_le_event_measure μ obs hObs P hP

/-- Scan error ≤ complement measure (with measurability). -/
theorem scanError_measure_le_complement [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    SPG.scanErrorMeasure μ obs P ≤ μ Pᶜ :=
  SPG.scanErrorMeasure_le_compl_measure μ obs hObs P hP

/-! ### Plan 23: Inverse Limit Structure -/

/-- Infinite stable words are determined by their prefix sequence. -/
theorem inverse_limit_extensionality (a b : X.XInfinity) :
    a = b ↔ ∀ m, X.prefixWord a m = X.prefixWord b m :=
  X.XInfinity_eq_iff a b

/-- The inverse limit equivalence round-trips (left). -/
theorem inverse_limit_round_left (F : X.CompatibleFamily) :
    X.toFamily (X.ofFamily F) = F :=
  X.inverseLimitEquiv_left_inv F

/-- The inverse limit equivalence round-trips (right). -/
theorem inverse_limit_round_right (a : X.XInfinity) :
    X.ofFamily (X.toFamily a) = a :=
  X.inverseLimitEquiv_right_inv a

/-! ### Plan 9 (partial): Fiber Structure -/

/-! ### Coverage: Ring/Field structure registrations -/

/-- X_m ≅ ZMod(F_{m+2}) ring isomorphism (coverage wrapper).
    thm:finite-resolution-mod -/
theorem stable_ring_isomorphism (m : Nat) :
    Nonempty (X m ≃+* ZMod (Nat.fib (m + 2))) := ⟨X.stableValueRingEquiv m⟩

/-- When F_{m+2} is prime, X_m admits a field structure (coverage wrapper).
    cor:field-phase-fib-prime -/
theorem stable_field_of_prime (hp : Nat.Prime (Nat.fib (m + 2))) :
    Nonempty (Field (X m)) := ⟨X.instFieldOfPrime hp⟩

/-- The ring characteristic of X_m equals F_{m+2}.
    thm:finite-resolution-mod -/
theorem ringChar_X_eq_fib (m : Nat) : ringChar (X m) = Nat.fib (m + 2) :=
  ringChar.eq_iff.mpr X.instCharP

/-- The stable value of Fold(w) is less than F_{m+4} (= |X_{m+2}|).
    prop:fold-basic -/
theorem stableValue_Fold_lt (w : Word (m + 2)) :
    stableValue (Fold w) < Nat.fib (m + 4) :=
  stableValue_lt_fib (Fold w)

end

end Omega.Frontier
