import Omega.Frontier.Conditional
import Omega.Folding.FiberArithmetic

namespace Omega.Frontier

noncomputable section


/-! ### Paper Proposition 3.x: Bayes Half-Bound -/

/-- Event mass + complement mass = total PMF mass (discrete partition). -/
theorem setMass_partition_discrete {α _β : Type*} [Fintype α]
    (μ : PMF α) (P : Set α) :
    SPG.setMass μ P + SPG.setMass μ Pᶜ = ∑ x, (μ x : ENNReal) :=
  SPG.setMass_add_setMass_compl μ P

/-- Total PMF mass over a Fintype is 1. -/
theorem PMF_total_mass_one {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ x, (μ x : ENNReal) = 1 :=
  SPG.PMF_sum_coe_eq_one μ

/-- Scan error is bounded by 1/2 for any PMF: 2 · ε ≤ 1 (paper Bayes optimality bound). -/
theorem scanError_bayes_half_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    2 * SPG.scanError μ obs P ≤ 1 :=
  SPG.two_mul_scanError_le_one μ obs P

/-! ### Paper Theorem 6.1: Stable Value Bound & Arithmetic -/

/-- Stable values are strictly bounded by the Fibonacci cardinality (paper Theorem 6.1). -/
theorem stableValue_bounded (x : X m) : stableValue x < Nat.fib (m + 2) :=
  stableValue_lt_fib x

/-- Stable values can be viewed as Fin-indexed values (paper Theorem 6.1). -/
theorem stableValue_as_fin (x : X m) :
    (X.stableValueFin x).val = stableValue x := rfl

/-- The stable value Fin map is injective. -/
theorem stableValueFin_injective_wrapper (m : Nat) :
    Function.Injective (X.stableValueFin (m := m)) :=
  X.stableValueFin_injective m

/-- Stable addition is commutative (paper Proposition 6.x). -/
theorem stableAdd_commutative (x y : X m) :
    X.stableAdd x y = X.stableAdd y x :=
  X.stableAdd_comm x y

/-- For n < F_{m+2}, X.ofNat m n has stable value n (paper Theorem 6.1 inverse). -/
theorem stableValue_ofNat_inverse {m : Nat} (n : Nat) (hn : n < Nat.fib (m + 2)) :
    stableValue (X.ofNat m n) = n :=
  X.stableValue_ofNat_lt n hn

/-- Stable value of ofNat respects modular reduction. -/
theorem stableValue_ofNat_mod_wrapper {m : Nat} (n : Nat) :
    stableValue (X.ofNat m (n % Nat.fib (m + 2))) = n % Nat.fib (m + 2) :=
  X.stableValue_ofNat_mod n

/-- stableZero has value 0. -/
theorem stableZero_value : stableValue (X.stableZero (m := m)) = 0 :=
  X.stableValue_stableZero

/-- Stable addition has a left identity. -/
theorem stableAdd_left_identity (x : X m) :
    X.stableAdd X.stableZero x = x :=
  X.stableAdd_zero_left x

/-- Stable addition has a right identity. -/
theorem stableAdd_right_identity (x : X m) :
    X.stableAdd x X.stableZero = x :=
  X.stableAdd_zero_right x

/-- Stable addition is associative (paper Section 6 emergent arithmetic). -/
theorem stableAdd_associative (x y z : X m) :
    X.stableAdd (X.stableAdd x y) z = X.stableAdd x (X.stableAdd y z) :=
  X.stableAdd_assoc x y z

/-- The stable syntax space is equivalent to Fin(F_{m+2}) as a finite type. -/
noncomputable def stableValueEquiv_wrapper (m : Nat) : X m ≃ Fin (Nat.fib (m + 2)) :=
  X.stableValueEquiv m

/-- The stableValue map into Fin is surjective (paper Theorem 6.1 surjectivity). -/
theorem stableValueFin_surjective_wrapper (m : Nat) :
    Function.Surjective (X.stableValueFin (m := m)) :=
  X.stableValueFin_surjective m

/-- The stableValue map into Fin is bijective (paper Theorem 6.1 bijectivity). -/
theorem stableValueFin_bijective_wrapper (m : Nat) :
    Function.Bijective (X.stableValueFin (m := m)) :=
  X.stableValueFin_bijective m

/-! ### Paper Theorem 4.2: Fiber Partition -/

/-- The word space has cardinality 2^m. -/
theorem word_card (m : Nat) : Fintype.card (Word m) = 2 ^ m :=
  X.Word_card m

/-- Fiber cardinalities sum to the total word count (paper Theorem 4.2: fibers partition). -/
theorem fiber_card_partition (m : Nat) :
    ∑ x : X m, (X.fiber x).card = Fintype.card (Word m) :=
  X.fiber_card_sum m

/-- Fiber cardinalities sum to 2^m. -/
theorem fiber_card_partition_pow (m : Nat) :
    ∑ x : X m, (X.fiber x).card = 2 ^ m :=
  X.fiber_card_sum_eq_pow m

/-! ### Paper Proposition 3.x: Complement Symmetry -/

/-- Discrete observable purity is symmetric under complement of the event. -/
theorem observablePure_compl_symmetric_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.ObservablePure μ obs Pᶜ ↔ SPG.ObservablePure μ obs P :=
  SPG.observablePure_compl μ obs P

/-- Discrete boundary cells are the same for the event and its complement. -/
theorem boundaryCells_compl_symmetric_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.boundaryCells μ obs Pᶜ = SPG.boundaryCells μ obs P :=
  SPG.boundaryCells_compl μ obs P

/-- Discrete prefix boundary cells are the same for the event and its complement. -/
theorem prefixBoundaryCells_compl_symmetric_discrete
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixBoundaryCells μ h Pᶜ = SPG.prefixBoundaryCells μ h P :=
  SPG.prefixBoundaryCells_compl μ h P

/-- Measure observable purity is symmetric under complement of the event. -/
theorem observablePure_compl_symmetric_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.ObservablePureMeasure μ obs Pᶜ ↔ SPG.ObservablePureMeasure μ obs P :=
  SPG.observablePureMeasure_compl μ obs P

/-- Measure boundary cells are the same for the event and its complement. -/
theorem boundaryCells_compl_symmetric_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.boundaryCellsMeasure μ obs Pᶜ = SPG.boundaryCellsMeasure μ obs P :=
  SPG.boundaryCellsMeasure_compl μ obs P

/-- Measure boundary cylinder count is the same for the event and its complement. -/
theorem boundaryCylinderCount_compl_symmetric_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.boundaryCylinderCount μ obs Pᶜ = SPG.boundaryCylinderCount μ obs P :=
  SPG.boundaryCylinderCount_compl μ obs P

/-- Measure prefix boundary cells are the same for the event and its complement. -/
theorem prefixBoundaryCells_compl_symmetric_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixBoundaryCellsMeasure μ h Pᶜ = SPG.prefixBoundaryCellsMeasure μ h P :=
  SPG.prefixBoundaryCellsMeasure_compl μ h P

/-- Measure prefix boundary cylinder count is the same for the event and its complement. -/
theorem prefixBoundaryCylinderCount_compl_symmetric_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixBoundaryCylinderCount μ h Pᶜ = SPG.prefixBoundaryCylinderCount μ h P :=
  SPG.prefixBoundaryCylinderCount_compl μ h P

/-! ### Paper Proposition 3.2: Cell-Level Bounds (measure) -/

/-- Cell event mass is bounded by cell total mass (measure). -/
theorem cellEventMeasure_le_cell [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) :
    SPG.cellEventMeasure μ obs P b ≤ SPG.cellMeasure μ obs b :=
  SPG.cellEventMeasure_le_cellMeasure μ obs P b

/-- Cell complement mass is bounded by cell total mass (measure). -/
theorem cellComplMeasure_le_cell [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) :
    SPG.cellComplMeasure μ obs P b ≤ SPG.cellMeasure μ obs b :=
  SPG.cellComplMeasure_le_cellMeasure μ obs P b

/-! ### Paper Proposition 3.2: Cell Partition Identity (measure, with measurability) -/

/-- Cell event mass + cell complement mass = total cell mass under a measurable event
    (measure-theoretic analogue of the discrete partition identity). -/
theorem cellPartition_identity_measure [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β)
    (hP : MeasurableSet P) :
    SPG.cellEventMeasure μ obs P b + SPG.cellComplMeasure μ obs P b = SPG.cellMeasure μ obs b :=
  SPG.cellEventMeasure_add_cellComplMeasure_eq_cellMeasure μ obs P b hP

/-! ### Paper Corollary 3.1: Direct Measure Observation Refinement Monotonicity -/

/-- Observation refinement reduces scan error (direct measure version, paper Corollary 3.1). -/
theorem scanError_measure_antitone_direct [MeasurableSpace α] [Fintype β] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq β]
    (μ : MeasureTheory.Measure α) (obs₁ : α → β) (obs₂ : α → γ)
    (f : γ → β) (hRef : ∀ x, obs₁ x = f (obs₂ x))
    (hObs₂ : Measurable obs₂) (P : Set α) (hP : MeasurableSet P) :
    SPG.scanErrorMeasure μ obs₂ P ≤ SPG.scanErrorMeasure μ obs₁ P :=
  SPG.scanErrorMeasure_antitone_of_refines μ obs₁ obs₂ f hRef hObs₂ P hP

/-! ### Paper Section POM: Fiber Multiplicity -/

/-- Fiber multiplicity: number of raw words folding to a given stable word. -/
theorem fiberMultiplicity_positive (x : X m) : 0 < X.fiberMultiplicity x :=
  X.fiberMultiplicity_pos x

/-- Fiber multiplicities sum to 2^m (paper POM fiber partition). -/
theorem fiberMultiplicity_sum (m : Nat) :
    ∑ x : X m, X.fiberMultiplicity x = 2 ^ m :=
  X.fiberMultiplicity_sum_eq_pow m

/-! ### Paper Proposition 3.2: Measure Cell Mass Sum Identities -/

/-- Cell event measures sum to the event measure (with measurability). -/
theorem cellEventMeasure_sum_eq_event [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    ∑ b, SPG.cellEventMeasure μ obs P b = μ P :=
  SPG.cellEventMeasure_sum μ obs hObs P hP

/-- Cell complement measures sum to the complement measure (with measurability). -/
theorem cellComplMeasure_sum_eq_compl [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    ∑ b, SPG.cellComplMeasure μ obs P b = μ Pᶜ :=
  SPG.cellComplMeasure_sum μ obs hObs P hP

/-- Cell total measures sum to the total measure (with measurability). -/
theorem cellMeasure_sum_eq_total [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs) :
    ∑ b, SPG.cellMeasure μ obs b = μ Set.univ :=
  SPG.cellMeasure_sum μ obs hObs

/-! ### Paper Defect Section: Zero Defect Characterization -/

/-- Local defect vanishes iff Fold commutes with restriction (paper Defect characterization). -/
theorem localDefect_zero_iff_fold_commutes (η : Word (m + 1)) :
    localDefect η = zeroWord m ↔ Fold (truncate η) = X.restrict (Fold η) :=
  localDefect_eq_zero_iff_fold_commutes η

/-- Global defect vanishes iff Fold commutes with restriction across resolutions. -/
theorem globalDefect_zero_iff (h : m ≤ n) (ω : Word n) :
    globalDefect h ω = zeroWord m ↔
      Fold (restrictWord h ω) = X.restrictLE h (Fold ω) :=
  globalDefect_eq_zero_iff h ω

/-- Non-curvature is equivalent to Fold-restriction commutativity. -/
theorem non_curvature_iff_commutes (η : Word (m + 1)) :
    ¬ localCurvature η ↔ Fold (truncate η) = X.restrict (Fold η) :=
  not_localCurvature_iff_fold_commutes η

/-! ### Paper Recursive Addressing: Prefix Determination -/

/-- Prefix determination is monotone in depth (paper prefix non-expansion). -/
theorem prefixDetermined_monotone {s : Set SPG.OmegaInfinity} {m n : Nat}
    (h : m ≤ n) (hs : SPG.PrefixDetermined s m) : SPG.PrefixDetermined s n :=
  SPG.prefixDetermined_of_le h hs

/-- Prefix-determined sets form a Boolean algebra (intersection). -/
theorem prefixDetermined_inter_closure {s t : Set SPG.OmegaInfinity} {m : Nat}
    (hs : SPG.PrefixDetermined s m) (ht : SPG.PrefixDetermined t m) :
    SPG.PrefixDetermined (s ∩ t) m :=
  SPG.prefixDetermined_inter hs ht

/-- Prefix-determined sets form a Boolean algebra (union). -/
theorem prefixDetermined_union_closure {s t : Set SPG.OmegaInfinity} {m : Nat}
    (hs : SPG.PrefixDetermined s m) (ht : SPG.PrefixDetermined t m) :
    SPG.PrefixDetermined (s ∪ t) m :=
  SPG.prefixDetermined_union hs ht

/-- Prefix-determined sets form a Boolean algebra (complement). -/
theorem prefixDetermined_compl_closure {s : Set SPG.OmegaInfinity} {m : Nat}
    (hs : SPG.PrefixDetermined s m) : SPG.PrefixDetermined sᶜ m :=
  SPG.prefixDetermined_compl hs

/-! ### Paper Section 6: Stable Multiplication & Ring Structure -/

/-- Stable multiplication is commutative. -/
theorem stableMul_commutative (x y : X m) :
    X.stableMul x y = X.stableMul y x :=
  X.stableMul_comm x y

/-- Stable multiplication distributes over stable addition. -/
theorem stableMul_distributes_left (x y z : X m) :
    X.stableMul x (X.stableAdd y z) = X.stableAdd (X.stableMul x y) (X.stableMul x z) :=
  X.stableMul_stableAdd_left x y z

/-- stableZero annihilates under multiplication. -/
theorem stableMul_zero (x : X m) : X.stableMul X.stableZero x = X.stableZero :=
  X.stableMul_zero_left x

/-- stableOne is the multiplicative identity (when F_{m+2} > 1). -/
theorem stableMul_one (hm : 1 < Nat.fib (m + 2)) (x : X m) :
    X.stableMul X.stableOne x = x :=
  X.stableMul_one_left hm x

/-- Stable multiplication is associative (paper Section 6). -/
theorem stableMul_associative (x y z : X m) :
    X.stableMul (X.stableMul x y) z = X.stableMul x (X.stableMul y z) :=
  X.stableMul_assoc x y z

/-- Fiber multiplicity depends only on the stable value index. -/
theorem fiberMultiplicity_value_dependent (x : X m) :
    X.fiberMultiplicity x = X.fiberMultiplicityByValue m (stableValue x) :=
  X.fiberMultiplicity_eq_byValue x

/-! ### Paper Theorem 4.1: Zeckendorf Bit Characterization -/

/-- The bit pattern of X.ofNat m n is given by the Zeckendorf representation (paper Theorem 4.1). -/
theorem zeckendorf_bit_characterization (n : Nat) {i : Nat} (h : i < m) :
    get (X.ofNat m n).1 i = true ↔ i + 2 ∈ Nat.zeckendorf n :=
  X.get_ofNat_eq_true_iff h

/-- Active positions of a stable word form a valid Zeckendorf representation. -/
theorem stable_zeckendorf_valid_wrapper (x : X m) :
    (X.zeckIndices x).IsZeckendorfRep :=
  X.zeckIndices_isZeckendorfRep x

/-! ### Paper Proposition 3.x: Scan Error Single-Sided Bounds -/

/-- Scan error is bounded by the event mass (discrete). -/
theorem scanError_le_event_mass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P ≤ SPG.setMass μ P :=
  SPG.scanError_le_setMass μ obs P

/-- Scan error is bounded by the complement mass (discrete). -/
theorem scanError_le_compl_mass {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P ≤ SPG.setMass μ Pᶜ :=
  SPG.scanError_le_setMass_compl μ obs P

/-! ### Paper Corollary 3.1: Measure Prefix Monotonicity & Probability Half-Bound -/

/-- Prefix scan error is monotonically non-increasing (direct measure version). -/
theorem prefixScanError_measure_antitone_direct {m₁ m₂ n : Nat}
    [MeasurableSpace (Word n)]
    [MeasurableSpace (Word m₂)] [MeasurableSingletonClass (Word m₂)]
    (μ : MeasureTheory.Measure (Word n))
    (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂)
    (hObs : Measurable (SPG.prefixObservation h₂))
    (P : Set (Word n)) (hP : MeasurableSet P) :
    SPG.prefixScanErrorMeasure μ h₂ P ≤ SPG.prefixScanErrorMeasure μ h₁ P :=
  SPG.prefixScanErrorMeasure_antitone_direct μ h₁ h₂ hm hObs P hP

/-- Scan error under a probability measure is bounded by 1/2 (measure version). -/
theorem scanError_measure_half_bound [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (obs : α → β) (hObs : Measurable obs) (P : Set α) (hP : MeasurableSet P) :
    2 * SPG.scanErrorMeasure μ obs P ≤ 1 :=
  SPG.scanErrorMeasure_le_half μ obs hObs P hP

/-! ### Paper Theorem 6.1: stableValue Range Characterization -/

/-- The range of stableValue is exactly {0,...,F_{m+2}-1}. -/
theorem stableValue_range_eq (m : Nat) :
    Set.range (stableValue (m := m)) = {n | n < Nat.fib (m + 2)} :=
  X.stableValue_range m

/-! ### Paper Defect Section: Defect Chain Structure -/

/-- The defect chain connects to the global defect. -/
theorem defectChain_is_globalDefect (m k : Nat) (x : X (m + k)) :
    defectChain m k x.1 = globalDefect (Nat.le_add_right m k) x.1 :=
  defectChain_stable m k x

/-! ### Paper Fold Section: Rewrite System Properties -/

/-- Each rewrite step preserves the Fibonacci value (already wrapped, for completeness). -/
theorem rewrite_value_preserved {a b : Rewrite.DigitCfg} (h : Rewrite.Step a b) :
    Rewrite.value b = Rewrite.value a :=
  Rewrite.step_value h

/-- Each rewrite step does not increase the mass (rewrite monotonicity). -/
theorem rewrite_mass_nonincreasing {a b : Rewrite.DigitCfg} (h : Rewrite.Step a b) :
    Rewrite.mass b ≤ Rewrite.mass a :=
  Rewrite.step_mass_le h

/-! ### Paper Graph Section: Golden-Mean Edge Structure -/

/-- The golden-mean graph has edges from state 0 to state 0 (via bit 0). -/
theorem goldenMean_allows_00 :
    Omega.Graph.goldenMeanGraph.edge false false false :=
  Omega.Graph.goldenMean_edge_ff

/-- The golden-mean graph has edges from state 0 to state 1 (via bit 1). -/
theorem goldenMean_allows_01 :
    Omega.Graph.goldenMeanGraph.edge false true true :=
  Omega.Graph.goldenMean_edge_ft

/-- The golden-mean graph has edges from state 1 to state 0 (via bit 0). -/
theorem goldenMean_allows_10 :
    Omega.Graph.goldenMeanGraph.edge true false false :=
  Omega.Graph.goldenMean_edge_tf

/-- The golden-mean graph forbids the 11 transition. -/
theorem goldenMean_forbids_11 (q' : Bool) :
    ¬ Omega.Graph.goldenMeanGraph.edge true true q' :=
  Omega.Graph.goldenMean_no_edge_tt q'

/-! ### Paper Section 6: Stable Value Homomorphism -/

/-- stableValue encodes addition modulo F_{m+2}. -/
theorem stableValue_add_homomorphism (x y : X m) :
    stableValue (X.stableAdd x y) = (stableValue x + stableValue y) % Nat.fib (m + 2) :=
  X.stableValue_stableAdd x y

/-- stableValue encodes multiplication modulo F_{m+2}. -/
theorem stableValue_mul_homomorphism (x y : X m) :
    stableValue (X.stableMul x y) = (stableValue x * stableValue y) % Nat.fib (m + 2) :=
  X.stableValue_stableMul x y

/-! ### Paper SPG Section: Cell Event Measure Monotonicity -/

/-- Cell event measure is monotone in the event (measure). -/
theorem cellEventMeasure_event_monotone [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) {P Q : Set α} (h : P ⊆ Q) (b : β) :
    SPG.cellEventMeasure μ obs P b ≤ SPG.cellEventMeasure μ obs Q b :=
  SPG.cellEventMeasure_mono μ obs h b

/-! ### Paper SPG Section: Cylinder & Prefix Resolution -/

/-- Prefix determination is closed under mixed-resolution intersections. -/
theorem prefixDetermined_inter_mixed {s t : Set SPG.OmegaInfinity} {m₁ m₂ : Nat}
    (hs : SPG.PrefixDetermined s m₁) (ht : SPG.PrefixDetermined t m₂) :
    SPG.PrefixDetermined (s ∩ t) (max m₁ m₂) :=
  SPG.prefixDetermined_inter_resolutions hs ht

/-! ### Paper Defect Section: Defect Resolution Structure -/

/-- Global defect at identity resolution is always zero. -/
theorem globalDefect_identity (ω : Word m) :
    globalDefect (Nat.le_refl m) ω = zeroWord m :=
  globalDefect_refl ω

/-- Global defect at adjacent resolutions equals local defect. -/
theorem globalDefect_adjacent (η : Word (m + 1)) :
    globalDefect (Nat.le_succ m) η = localDefect η :=
  globalDefect_succ η

/-! ### Paper Fold Section: Rewrite Chain Properties -/

/-- Mass is non-increasing along rewrite chains. -/
theorem rewrite_mass_chain_nonincreasing {a b : Rewrite.DigitCfg}
    (h : Relation.ReflTransGen Rewrite.Step a b) :
    Rewrite.mass b ≤ Rewrite.mass a :=
  Rewrite.reflTransGen_mass_le h

/-! ### Paper Section 4: Weight & Append Structure -/

/-- Weight is preserved under appending false (extending by zero bit). -/
theorem weight_preserved_appendFalse (x : X m) :
    weight (X.appendFalse x).1 = weight x.1 :=
  weight_appendFalse x

/-- Weight increases by F(m+2) under appending true. -/
theorem weight_increases_appendTrue (x : X m) (hLast : get x.1 (m - 1) = false) :
    weight (X.appendTrue x hLast).1 = weight x.1 + Nat.fib (m + 2) :=
  weight_appendTrue x hLast

/-- The constant observation has a single cell covering everything. -/
theorem constant_observation_cell (c : β) :
    SPG.observableCell (fun _ : α => c) c = Set.univ :=
  SPG.observableCell_const_eq_univ c

/-! ### Paper POM Section: Carry Defect Structure -/

/-- stableValue decomposes as restrict value + last bit contribution. -/
theorem stableValue_last_bit_decomposition (x : X (m + 1)) :
    stableValue x = stableValue (X.restrict x) +
      (if x.1 ⟨m, Nat.lt_succ_self m⟩ = true then Nat.fib (m + 2) else 0) :=
  stableValue_eq_restrict_add_last x

/-- The carry indicator is bounded by 1. -/
theorem carry_indicator_bounded (x y : X (m + 1)) :
    carryIndicator x y ≤ 1 :=
  X.carryIndicator_le_one x y

/-! ### Paper InverseLimit: Extensionality -/

/-- Infinite stable words are uniquely determined by their prefixes. -/
theorem XInfinity_uniqueness {a b : X.XInfinity} (h : ∀ m, X.prefixWord a m = X.prefixWord b m) :
    a = b :=
  X.XInfinity_ext h

/-- Zeckendorf indices have length at most m. -/
theorem zeckIndices_bounded (x : X m) : (X.zeckIndices x).length ≤ m :=
  X.zeckIndices_length_le x

/-! ### Paper SPG Section: Boundary Cell & Scan Error Structure -/

/-- Boundary cell count is bounded by the total number of observation cells. -/
theorem boundaryCells_count_bounded {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    (SPG.boundaryCells μ obs P).card ≤ Fintype.card β :=
  SPG.boundaryCells_card_le μ obs P

/-- Observable events from coarser observables have at most the same error under finer observables. -/
theorem observable_event_refined_monotone {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (A : Set β) :
    SPG.scanError μ obs₂ (SPG.observableEvent obs₁ A) ≤
      SPG.scanError μ obs₁ (SPG.observableEvent obs₁ A) :=
  SPG.scanError_observableEvent_refines_zero μ obs₁ obs₂ f hRef A

/-- Cell complement measure is anti-monotone in event containment. -/
theorem cellComplMeasure_antimonotone [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) {P Q : Set α} (h : P ⊆ Q) (b : β) :
    SPG.cellComplMeasure μ obs Q b ≤ SPG.cellComplMeasure μ obs P b :=
  SPG.cellComplMeasure_anti μ obs h b

/-! ### Paper Defect Section: xor-truncation compatibility -/

/-- Truncation distributes over xor of words. -/
theorem truncate_distributes_xor (a b : Word (m + 1)) :
    truncate (xorWord a b) = xorWord (truncate a) (truncate b) :=
  truncate_xorWord a b

/-! ### Paper POM Section: Value-Restriction Modular Arithmetic -/

/-- stableValue(restrict x) ≡ stableValue(x) mod F_{m+2} (paper POM modular identity). -/
theorem stableValue_restrict_modular (x : X (m + 1)) :
    stableValue x % Nat.fib (m + 2) = stableValue (X.restrict x) % Nat.fib (m + 2) :=
  stableValue_restrict_mod x

/-- Carry indicator is zero when sum is below threshold. -/
theorem carry_zero_below_threshold (x y : X (m + 1))
    (h : stableValue x + stableValue y < Nat.fib (m + 3)) :
    carryIndicator x y = 0 :=
  carryIndicator_zero_of_lt x y h

/-- Carry indicator is one when sum reaches threshold. -/
theorem carry_one_above_threshold (x y : X (m + 1))
    (h : stableValue x + stableValue y ≥ Nat.fib (m + 3)) :
    carryIndicator x y = 1 :=
  carryIndicator_one_of_ge x y h

/-! ### Paper POM Theorem: Carry-Free Restriction Identity -/

/-- When stable addition doesn't overflow, restriction commutes with addition modulo F_{m+2}
    (paper POM carry defect theorem, zero-carry case). -/
theorem restrict_stableAdd_no_carry (x y : X (m + 1))
    (h : stableValue x + stableValue y < Nat.fib (m + 3)) :
    stableValue (X.restrict (X.stableAdd x y)) % Nat.fib (m + 2) =
      (stableValue (X.restrict x) + stableValue (X.restrict y)) % Nat.fib (m + 2) :=
  X.restrict_stableAdd_of_no_carry x y h

end

end Omega.Frontier
