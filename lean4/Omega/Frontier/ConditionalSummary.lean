import Omega.Frontier.ConditionalArithmetic
import Omega.Folding.MomentSum

namespace Omega.Frontier

noncomputable section


/-- Fiber membership is characterized by the Fold map. -/
theorem fiber_membership_iff (x : X m) (w : Word m) :
    w ∈ X.fiber x ↔ Fold w = x :=
  X.mem_fiber_iff_fold x w

/-- The modular projection is surjective: every element of X_m
    is the projection of some element of X_{m+1}. -/
theorem modular_project_surjective (m : Nat) :
    Function.Surjective (X.modularProject (m := m)) :=
  X.modularProject_surjective m

/-! ### Plans 17/18: Measure Event/Complement Bounds (named) -/

/-- Scan error ≤ event measure (named). -/
theorem scan_error_le_event [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    SPG.scanErrorMeasure μ obs P ≤ μ P :=
  SPG.scanErrorMeasure_le_event_measure μ obs hObs P hP

/-- Scan error ≤ complement measure (named). -/
theorem scan_error_le_compl [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    SPG.scanErrorMeasure μ obs P ≤ μ Pᶜ :=
  SPG.scanErrorMeasure_le_compl_measure μ obs hObs P hP

/-! ### Scan Error Cell-Level Properties -/

/-- When all cells are pure, scan error vanishes. -/
theorem all_pure_zero_error {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (h : ∀ b, SPG.cellEventMass μ obs P b = 0 ∨ SPG.cellComplMass μ obs P b = 0) :
    SPG.scanError μ obs P = 0 :=
  SPG.scanError_zero_of_all_pure μ obs P h

/-- Cell event mass equals full cell mass for members of the observable set. -/
theorem cell_mass_for_member {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (A : Set β) (b : β) (hb : b ∈ A) :
    SPG.cellEventMass μ obs (SPG.observableEvent obs A) b = SPG.cellMass μ obs b :=
  SPG.cellEventMass_of_mem_observableEvent μ obs A b hb

/-! ### Defect Chain Recursion -/

/-- The xor operation is involutive: (a ⊕ b) ⊕ b = a. -/
theorem xor_involution (a b : Word m) :
    xorWord (xorWord a b) b = a :=
  xorWord_xor_cancel_right a b

/-- Defect chain unfolds recursively: chain(k+1) = localDefect ⊕ chain(k). -/
theorem defect_chain_recursion (m k : Nat) (ω : Word (m + k + 1)) :
    defectChain m (k + 1) ω =
      xorWord (restrictWord (Nat.le_add_right m k) (localDefect ω))
        (defectChain m k (truncate ω)) :=
  defectChain_succ m k ω

/-! ### Measure Min Bound & Boundary Count -/

/-- Scan error ≤ min(μ(P), μ(Pᶜ)) with measurability. -/
theorem scan_error_measure_min_bound [MeasurableSpace α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (hObs : Measurable obs)
    (P : Set α) (hP : MeasurableSet P) :
    SPG.scanErrorMeasure μ obs P ≤ min (μ P) (μ Pᶜ) :=
  SPG.scanErrorMeasure_le_min_event_compl μ obs hObs P hP

/-- Observable events have zero boundary count (measure, named). -/
theorem boundary_zero_for_observable [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.boundaryCylinderCount μ obs (SPG.observableEvent obs A) = 0 :=
  SPG.boundaryCylinderCount_observable_zero μ obs A

/-! ### Ring Idempotents -/

/-- 0 + 0 = 0 in the stable ring. -/
theorem zero_plus_zero : X.stableAdd (X.stableZero (m := m)) X.stableZero = X.stableZero :=
  X.stableAdd_zero_zero

/-- 0 * 0 = 0 in the stable ring. -/
theorem zero_times_zero : X.stableMul (X.stableZero (m := m)) X.stableZero = X.stableZero :=
  X.stableMul_zero_zero

/-- 1 * 1 = 1 in the stable ring (for m ≥ 1). -/
theorem one_times_one (hm : 1 < Nat.fib (m + 2)) :
    X.stableMul (X.stableOne (m := m)) X.stableOne = X.stableOne :=
  X.stableMul_one_one hm

/-! ### Complete Summary: All Major Paper Results Formalized -/

/-! #### 1. Fibonacci & Cardinality -/

/-- F_0 = 1, F_1 = 1, F_2 = 2 (paper convention). -/
theorem fib_initial : Nat.fib 1 = 1 ∧ Nat.fib 2 = 1 ∧ Nat.fib 3 = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- F_{k+2} = F_{k+1} + F_k (Fibonacci recurrence). -/
theorem fib_fibonacci (k : Nat) : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) :=
  fib_succ_succ' (k + 1)

/-- |X_m| = F_{m+2} (fundamental cardinality theorem). -/
theorem stable_syntax_cardinality (m : Nat) : Fintype.card (X m) = Nat.fib (m + 2) :=
  X.card_eq_fib m

/-! #### 2. Fold Map -/

/-- Fold is a retraction: Fold ∘ Fold = Fold. -/
theorem fold_retraction (w : Word m) : Fold (Fold w).1 = Fold w :=
  Fold_idempotent w

/-- Fold restricted to stable words is the identity. -/
theorem fold_identity_on_stable (x : X m) : Fold x.1 = x :=
  Fold_stable x

/-! #### 3. Rewrite System -/

/-- The rewrite relation terminates: well-founded. -/
theorem rewrite_terminates : WellFounded (flip Rewrite.Step) :=
  Rewrite.step_stronglyTerminating

/-- Rewrite steps preserve value. -/
theorem rewrite_preserves_value {a b : Rewrite.DigitCfg} (h : Rewrite.Step a b) :
    Rewrite.value b = Rewrite.value a :=
  Rewrite.step_value h

/-! #### 4. Scan Error Theory -/

/-- Zero scan error ↔ all cells pure (discrete). -/
theorem zero_error_iff_pure {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P = 0 ↔ SPG.ObservablePure μ obs P :=
  SPG.scanError_eq_zero_iff_observablePure μ obs P

/-- Finer observation always reduces error (discrete). -/
theorem finer_observation_less_error {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (P : Set α) :
    SPG.scanError μ obs₂ P ≤ SPG.scanError μ obs₁ P :=
  SPG.scanError_antitone_of_refines μ obs₁ obs₂ f hRef P

/-! #### 5. Stable Arithmetic -/

/-- X_m ≅ ℤ/F_{m+2}ℤ as commutative rings (complete summary). -/
theorem stable_ring_structure (m : Nat) :
    -- Additive group
    (∀ x y : X m, X.stableAdd x y = X.stableAdd y x) ∧
    (∀ x y z : X m, X.stableAdd (X.stableAdd x y) z = X.stableAdd x (X.stableAdd y z)) ∧
    (∀ x : X m, X.stableAdd X.stableZero x = x) ∧
    (∀ x : X m, X.stableAdd x (X.stableNeg x) = X.stableZero) ∧
    -- Multiplicative monoid
    (∀ x y : X m, X.stableMul x y = X.stableMul y x) ∧
    (∀ x y z : X m, X.stableMul (X.stableMul x y) z = X.stableMul x (X.stableMul y z)) ∧
    -- Distributivity
    (∀ x y z : X m, X.stableMul x (X.stableAdd y z) =
      X.stableAdd (X.stableMul x y) (X.stableMul x z)) :=
  ⟨X.stableAdd_comm, X.stableAdd_assoc, X.stableAdd_zero_left, X.stableAdd_stableNeg,
   X.stableMul_comm, X.stableMul_assoc, X.stableMul_stableAdd_left⟩

/-! #### 6. Inverse Limit -/

/-- Concrete inverse limit: CompatibleFamily ≃ XInfinity. -/
noncomputable def concrete_inverse_limit : X.CompatibleFamily ≃ X.XInfinity :=
  X.inverseLimitEquiv

/-! #### 7. Sofic Representation -/

/-- Stable language = Golden-mean sofic language. -/
theorem stable_equals_sofic (m : Nat) :
    {w : Word m | No11 w} =
      {w : Word m | Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w} :=
  Omega.Graph.stableLanguage_eq_goldenMean m

/-! #### 8. Defect Theory -/

/-- Zero defect ↔ Fold commutes with restriction. -/
theorem zero_defect_iff_commutes (η : Word (m + 1)) :
    localDefect η = zeroWord m ↔ Fold (truncate η) = X.restrict (Fold η) :=
  localDefect_eq_zero_iff_fold_commutes η

/-- Global defect decomposes as xor-telescope. -/
theorem defect_is_telescope (m k : Nat) (ω : Word (m + k)) :
    globalDefect (Nat.le_add_right m k) ω = defectChain m k ω :=
  globalDefect_eq_defectChain m k ω

/-! #### Stable Arithmetic: Doubling -/

/-- x + x = 2·x in the stable ring (for F_{m+2} > 2). -/
theorem doubling_eq_two_mul (x : X m) (hm : 2 < Nat.fib (m + 2)) :
    X.stableAdd x x = X.stableMul (X.ofNat m 2) x :=
  X.stableAdd_self_eq_stableMul_two x hm

/-! #### Scan Error Named Variants -/

/-- Purity implies zero scan error (discrete, named). -/
theorem pure_means_zero {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (h : SPG.ObservablePure μ obs P) :
    SPG.scanError μ obs P = 0 :=
  SPG.purity_implies_zero_error μ obs P h

/-- Scan error complement symmetry (discrete, named). -/
theorem error_is_complement_symmetric {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs Pᶜ = SPG.scanError μ obs P :=
  SPG.error_complement_symmetry μ obs P

/-! #### Defect Theory: Accumulated Commutativity Failure -/

/-- Local defect characterizes one-step Fold commutativity (named). -/
theorem local_defect_characterizes (η : Word (m + 1)) :
    localDefect η = zeroWord m ↔ Fold (truncate η) = X.restrict (Fold η) :=
  localDefect_characterizes_fold η

/-- Global defect characterizes multi-step Fold commutativity (named). -/
theorem global_defect_characterizes (h : m ≤ n) (ω : Word n) :
    globalDefect h ω = zeroWord m ↔
      Fold (restrictWord h ω) = X.restrictLE h (Fold ω) :=
  globalDefect_accumulated h ω

/-- xor is left-cancellative: a ⊕ b = a ⊕ c → b = c. -/
theorem xor_left_cancel {a b c : Word m} (h : xorWord a b = xorWord a c) : b = c :=
  xorWord_left_cancel h

/-! #### Negation Properties -/

/-- Negation is injective in the stable ring. -/
theorem stable_neg_injective : Function.Injective (X.stableNeg (m := m)) :=
  X.stableNeg_injective

/-- Negation is surjective in the stable ring. -/
theorem stable_neg_surjective : Function.Surjective (X.stableNeg (m := m)) :=
  X.stableNeg_surjective

/-- Negation is bijective in the stable ring. -/
theorem stable_neg_bijective : Function.Bijective (X.stableNeg (m := m)) :=
  X.stableNeg_bijective

/-! #### Scan Error & Boundary Summary -/

/-- Zero error ↔ zero boundary count (measure). -/
theorem zero_error_iff_zero_boundary [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P = 0 ↔ SPG.boundaryCylinderCount μ obs P = 0 :=
  SPG.scanError_zero_iff_boundary_zero μ obs P

/-! #### Fiber Unique Decomposition -/

/-- Every word belongs to exactly one Fold fiber (unique decomposition). -/
theorem unique_fiber_decomposition (w : Word m) :
    ∃! x : X m, w ∈ X.fiber x :=
  X.word_in_unique_fiber w

/-- Fold maps to a unique stable target. -/
theorem fold_unique (w : Word m) : ∃! x : X m, Fold w = x :=
  X.Fold_unique_target w

/-! #### Group Action & Subtraction -/

/-- Addition by x is a bijection on X_m (free group action). -/
theorem stableAdd_is_bijection (x : X m) :
    Function.Bijective (X.stableAdd x) :=
  X.stableAdd_bijective x

/-- x - 0 = x. -/
theorem sub_zero (x : X m) : X.stableSub x X.stableZero = x :=
  X.stableSub_zero x

/-- 0 - x = -x. -/
theorem zero_sub (x : X m) : X.stableSub X.stableZero x = X.stableNeg x :=
  X.zero_stableSub x

/-- Negation is an involution (Function.Involutive). -/
theorem neg_involutive : Function.Involutive (X.stableNeg (m := m)) :=
  X.stableNeg_involutive

/-! #### Growth Bounds & Prefix Scan Error -/

/-- F_{m+2} ≤ 2^m: Fibonacci is subexponential. -/
theorem fibonacci_subexponential (m : Nat) : Nat.fib (m + 2) ≤ 2 ^ m :=
  X.fib_le_pow_two m

/-- |X_m| ≤ 2^m: stable words are a fraction of all words. -/
theorem stable_words_bounded (m : Nat) : Fintype.card (X m) ≤ 2 ^ m :=
  X.stable_card_le_pow m

/-- Prefix scan error is bounded by 1/2 at any resolution. -/
theorem prefix_error_half_bound (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    2 * SPG.prefixScanError μ h P ≤ 1 :=
  SPG.prefixScanError_le_half μ h P

/-- Fold output is always a stable (No11) word. -/
theorem fold_output_stable (w : Word m) : No11 (Fold w).1 :=
  X.Fold_maps_to_stable w

/-! #### Observable Event Preimage Characterization -/

/-- Observable events are preimages of the observation map. -/
theorem observable_event_is_preimage {α β : Type*} (obs : α → β) (A : Set β) :
    SPG.observableEvent obs A = obs ⁻¹' A :=
  SPG.observableEvent_eq_preimage obs A

/-- Observable cells are preimages of singletons. -/
theorem observable_cell_is_preimage {α β : Type*} (obs : α → β) (b : β) :
    SPG.observableCell obs b = obs ⁻¹' {b} :=
  SPG.observableCell_eq_preimage obs b

/-- Every element belongs to its observation cell. -/
theorem element_in_own_cell {α β : Type*} (obs : α → β) (x : α) :
    x ∈ SPG.observableCell obs (obs x) :=
  SPG.observableCell_covers obs x

/-! #### Modular Projection Multiplication -/

/-- Modular projection preserves multiplication (no-carry case). -/
theorem modular_project_mul_no_carry (x y : X (m + 1))
    (h : stableValue x * stableValue y < Nat.fib (m + 3)) :
    X.modularProject (X.stableMul x y) =
      X.stableMul (X.modularProject x) (X.modularProject y) :=
  X.modularProject_mul_no_carry x y h

/-! #### Plan 2: Integral Domain & Prime Field -/

/-- When F_{m+2} is prime, X_m is an integral domain (no zero divisors). -/
theorem integral_domain_when_prime (hPrime : Nat.Prime (Nat.fib (m + 2)))
    {x y : X m} (hx : x ≠ X.stableZero) (hy : y ≠ X.stableZero) :
    X.stableMul x y ≠ X.stableZero :=
  X.stableMul_no_zero_divisor_of_prime hPrime hx hy

/-! #### Cell-Local Measure Dependence -/

/-- Cell event measure depends only on intersection with cell (measure). -/
theorem cell_event_local [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) {P Q : Set α} (b : β)
    (h : P ∩ SPG.observableCell obs b = Q ∩ SPG.observableCell obs b) :
    SPG.cellEventMeasure μ obs P b = SPG.cellEventMeasure μ obs Q b :=
  SPG.cellEventMeasure_depends_on_inter μ obs b h

/-! #### Plan 2: Concrete Prime Fields -/

/-- X_2 ≅ F_3 is a field (F_3 = 3 is prime). -/
theorem X2_is_field : Nat.Prime (Nat.fib 4) := X.X2_is_integral_domain

/-- X_3 ≅ F_5 is a field (F_5 = 5 is prime). -/
theorem X3_is_field : Nat.Prime (Nat.fib 5) := X.F4_is_prime

/-- X_4 ≅ ℤ/8ℤ is NOT a field (F_5 = 8 not prime). -/
theorem X4_not_field : ¬ Nat.Prime (Nat.fib 6) := X.F5_not_prime

/-! #### xor-Restrict Exchange -/

/-- Restriction distributes over xor (named). -/
theorem restrict_distributes_xor (h : m ≤ n) (a b : Word n) :
    restrictWord h (xorWord a b) = xorWord (restrictWord h a) (restrictWord h b) :=
  restrictWord_xorWord h a b

/-! #### Fibonacci Primality & Field Resolutions -/

/-- X_1 ≅ F_2 is a field (F_2 = 2 prime). -/
theorem X1_is_field : Nat.Prime (Nat.fib 3) := X.F2_is_prime

/-- X_5 ≅ F_6 is a field (F_6 = 13 prime). -/
theorem X5_is_field : Nat.Prime (Nat.fib 7) := X.F6_is_prime

/-- X_9 ≅ F_10 is a field (F_10 = 89 prime). -/
theorem X9_is_field : Nat.Prime (Nat.fib 11) := X.F10_is_prime

/-- The 5 Fibonacci primes in F_2..F_11: 2, 3, 5, 13, 89. -/
theorem fibonacci_primes_census :
    Nat.Prime (Nat.fib 3) ∧ Nat.Prime (Nat.fib 4) ∧ Nat.Prime (Nat.fib 5) ∧
    Nat.Prime (Nat.fib 7) ∧ Nat.Prime (Nat.fib 11) :=
  X.fibonacci_prime_list

/-! #### Purity & Boundary Equivalence -/

/-- Purity ↔ empty boundary (discrete, named). -/
theorem purity_iff_boundary {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.ObservablePure μ obs P ↔ SPG.boundaryCells μ obs P = ∅ :=
  SPG.pure_iff_zero_boundary μ obs P

/-- Boundary count is complement-symmetric (discrete, named). -/
theorem boundary_count_symmetric {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    (SPG.boundaryCells μ obs Pᶜ).card = (SPG.boundaryCells μ obs P).card :=
  SPG.boundary_cells_symmetric μ obs P

/-! #### Fibonacci Composite Census -/

/-- The 5 composite Fibonacci values in F_2..F_11: 8, 21, 34, 55, 144. -/
theorem fibonacci_composites :
    ¬ Nat.Prime (Nat.fib 6) ∧ ¬ Nat.Prime (Nat.fib 8) ∧
    ¬ Nat.Prime (Nat.fib 9) ∧ ¬ Nat.Prime (Nat.fib 10) ∧
    ¬ Nat.Prime (Nat.fib 12) :=
  X.fibonacci_composite_list

/-! #### Prefix Event Purity (Measure) -/

/-- Prefix events are pure for the prefix observation (measure). -/
theorem prefix_event_pure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.ObservablePureMeasure μ (SPG.prefixObservation h) (SPG.prefixEvent h A) :=
  SPG.prefixEvent_is_pure μ h A

/-- Prefix scan error at own resolution vanishes (measure). -/
theorem prefix_error_vanishes_at_own [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixScanErrorMeasure μ h (SPG.prefixEvent h A) = 0 :=
  SPG.prefixScanErrorMeasure_at_own_resolution μ h A

/-! #### Value Round-Trips & Bounds -/

/-- ofNat(stableValue(x)) = x (round-trip, named). -/
theorem value_ofNat_roundtrip (x : X m) : X.ofNat m (stableValue x) = x :=
  X.ofNat_of_stableValue x

/-- stableValue(Fold(x.1)) = stableValue(x) (Fold-value roundtrip). -/
theorem fold_value_roundtrip (x : X m) : stableValue (Fold x.1) = stableValue x :=
  X.Fold_stableValue_roundtrip x

/-- Arithmetic operations preserve the Fibonacci bound. -/
theorem add_preserves_bound (x y : X m) : stableValue (X.stableAdd x y) < Nat.fib (m + 2) :=
  X.stableAdd_value_bound x y

/-- Multiplication preserves the Fibonacci bound. -/
theorem mul_preserves_bound (x y : X m) : stableValue (X.stableMul x y) < Nat.fib (m + 2) :=
  X.stableMul_value_bound x y

/-- stableValue is strictly less than 2^m. -/
theorem value_lt_two_pow (x : X m) : stableValue x < 2 ^ m :=
  X.stableValue_lt_pow x

/-! #### Inverse Limit Bijectivity -/

/-- The inverse limit map ofFamily is bijective. -/
theorem inverse_limit_bijective :
    Function.Bijective (X.ofFamily : X.CompatibleFamily → X.XInfinity) :=
  X.CompatibleFamily_complete

/-! #### Clopen Topology -/

/-- The complement of a fromWordSet is clopen. -/
theorem fromWordSet_complement_clopen (A : Set (Word m)) :
    IsClopen (SPG.fromWordSet Aᶜ) :=
  SPG.fromWordSet_compl_is_clopen A

/-! #### Scan Error Global Bound -/

/-- Scan error is always ≤ 1 for a PMF. -/
theorem scan_error_le_one {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P ≤ 1 :=
  SPG.scanError_le_one μ obs P

/-! #### Higher Cardinalities & Primality -/

/-- |X_11| = 233. -/
theorem card_stable_eleven : Fintype.card (X 11) = 233 := X.card_X_eleven

/-- |X_12| = 377. -/
theorem card_stable_twelve : Fintype.card (X 12) = 377 := X.card_X_twelve

/-- |X_13| = 610. -/
theorem card_stable_thirteen : Fintype.card (X 13) = 610 := X.card_X_thirteen

/-- F_12 = 233 is prime (X_11 is a field). -/
theorem X11_is_field : Nat.Prime (Nat.fib 13) := X.F12_is_prime

/-! #### Carry Element & Modular Projection -/

/-- Carry element value: stableValue(χ^car_m) = Nat.fib m. -/
theorem carry_element_val :
    stableValue (X.carryElement m) = Nat.fib m :=
  X.carryElement_value

/-- Modular projection preserves zero. -/
theorem modular_preserves_zero :
    X.modularProject (X.stableZero (m := m + 1)) = X.stableZero :=
  X.modularProject_preserves_zero

/-! #### Ring Order & Neg-One -/

/-- The ring order (number of elements) is F_{m+2}. -/
theorem ring_has_fibonacci_order (m : Nat) : Fintype.card (X m) = Nat.fib (m + 2) :=
  X.stable_ring_order m

/-- -1 has value F_{m+2} - 1 (maximal element). -/
theorem neg_one_is_maximal_element (hm : 1 ≤ m) :
    stableValue (X.stableNeg (X.stableOne (m := m))) = Nat.fib (m + 2) - 1 :=
  X.neg_one_value hm

/-- stableValue < 2^m (exponential bound). -/
theorem value_exponential_bound (x : X m) : stableValue x < 2 ^ m :=
  X.stableValue_lt_pow x

/-! #### xor Group Structure -/

/-- xor is associative. -/
theorem xor_associative (a b c : Word m) :
    xorWord (xorWord a b) c = xorWord a (xorWord b c) :=
  xorWord_is_associative a b c

/-- xor is commutative. -/
theorem xor_commutative (a b : Word m) :
    xorWord a b = xorWord b a :=
  xorWord_is_commutative a b

/-- Zero is the xor identity. -/
theorem xor_identity (a : Word m) :
    xorWord a (zeroWord m) = a :=
  xorWord_zero_id a

/-- xor is self-inverse. -/
theorem xor_self_inverse (a : Word m) :
    xorWord a a = zeroWord m :=
  xorWord_self a

/-! #### Prefix Error Bounds -/

/-- Prefix error ≤ 1 (global bound). -/
theorem prefix_error_le_one (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanError μ h P ≤ 1 :=
  SPG.prefixScanError_le_one μ h P

/-- Cell mass total equals setMass(univ). -/
theorem cell_mass_total {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    ∑ b, SPG.cellMass μ obs b = SPG.setMass μ Set.univ :=
  SPG.cellMass_total μ obs

/-! #### Fiber Decomposition Completeness -/

/-- Complete fiber decomposition: uniqueness + positivity + partition sum. -/
theorem fiber_decomposition (m : Nat) :
    (∀ w : Word m, ∃! x : X m, w ∈ X.fiber x) ∧
    (∀ x : X m, 0 < (X.fiber x).card) ∧
    (∑ x : X m, (X.fiber x).card = 2 ^ m) :=
  X.fiber_decomposition_complete m

/-- Fold always outputs a stable (No11) word. -/
theorem fold_always_stable (w : Word m) : No11 (Fold w).1 :=
  X.Fold_output_is_stable w

/-! ### POM coverage: projection entropy & moment sums -/

/-- |X_m| = F_{m+2} (projection entropy cardinality).
    prop:pom-projection-entropy -/
theorem projection_entropy_cardinality (m : Nat) :
    Fintype.card (X m) = Nat.fib (m + 2) := X.card_eq_fib m

/-- Fiber multiplicities sum to 2^m.
    prop:pom-fiber-sum-identity -/
theorem fiber_sum_eq_pow (m : Nat) :
    ∑ x : X m, X.fiberMultiplicity x = 2 ^ m := X.fiberMultiplicity_sum_eq_pow m

/-- Cauchy-Schwarz collision bound: (2^m)² ≤ F_{m+2} · S_2(m).
    thm:fold-collision-convex-lower-bounds -/
theorem cauchy_schwarz_collision_bound (m : Nat) :
    (2 ^ m) ^ 2 ≤ Nat.fib (m + 2) * momentSum 2 m := momentSum_cauchy_schwarz m

/-- S_q is monotone in q.
    prop:pom-sq-monotone -/
theorem moment_monotone (q m : Nat) (hq : 1 ≤ q) :
    momentSum q m ≤ momentSum (q + 1) m := momentSum_mono_q q m hq

/-- S_q(m) ≥ F_{m+2} for all q.
    prop:pom-sq-lower -/
theorem moment_ge_cardinality (q m : Nat) :
    Nat.fib (m + 2) ≤ momentSum q m := momentSum_ge_card q m

/-- S_2(m) ≥ 2^m (collision sum lower bound).
    cor:pom-s2-lower -/
theorem collision_sum_ge_pow (m : Nat) :
    2 ^ m ≤ momentSum 2 m := Omega.momentSum_two_ge_pow m

/-! ### POM existence registrations -/

/-- The maximum fiber multiplicity is achieved by some stable word.
    thm:pom-max-fiber-achieved -/
theorem max_fiber_achieved (m : Nat) :
    ∃ x : X m, X.fiberMultiplicity x = X.maxFiberMultiplicity m :=
  X.maxFiberMultiplicity_achieved m

/-- For m ≥ 2, some stable word has fiber multiplicity ≥ 2 (pigeonhole).
    prop:pom-fiber-pigeonhole -/
theorem fiber_pigeonhole (m : Nat) (hm : 2 ≤ m) :
    ∃ x : X m, 2 ≤ X.fiberMultiplicity x :=
  Omega.exists_fiber_ge_two m hm

/-- The maximum fiber multiplicity is always positive.
    thm:pom-max-fiber-positive -/
theorem max_fiber_positive (m : Nat) : 0 < X.maxFiberMultiplicity m :=
  X.maxFiberMultiplicity_pos m

/-- D(m+2) ≤ D(m+1) + D(m) (Fibonacci-type upper bound on max fiber).
    cor:pom-D-rec-upper -/
theorem max_fiber_fib_bound (m : Nat) :
    X.maxFiberMultiplicity (m + 2) ≤ X.maxFiberMultiplicity (m + 1) + X.maxFiberMultiplicity m :=
  X.maxFiberMultiplicity_le_add m

/-! ### Entropy rate discrete skeleton -/

/-- F_{m+2} < 2^m for m ≥ 2 (strict entropy gap).
    prop:pom-projection-entropy-strict -/
theorem entropy_gap_strict (m : Nat) (hm : 2 ≤ m) : Nat.fib (m + 2) < 2 ^ m := by
  have key : ∀ n, 2 ≤ n → Nat.fib (n + 2) < 2 ^ n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => omega
      | succ k =>
        cases k with
        | zero => native_decide
        | succ k =>
          have hR := Omega.fib_succ_succ' (k + 3)
          have ihk : Nat.fib (k + 4) < 2 ^ (k + 2) := ih (by omega)
          have ih0 : Nat.fib (k + 3) ≤ 2 ^ (k + 2) := Omega.fib_le_pow_two (k + 1)
          calc Nat.fib (k + 2 + 1 + 2)
              = Nat.fib (k + 4) + Nat.fib (k + 3) := hR
            _ < 2 ^ (k + 2) + 2 ^ (k + 2) := Nat.add_lt_add_of_lt_of_le ihk ih0
            _ = 2 ^ (k + 2 + 1) := by ring
  exact key m hm

/-- F_{m+3} ≤ 2 · F_{m+2} (projection ratio bound).
    prop:pom-projection-ratio-decreasing -/
theorem projection_ratio_decreasing (m : Nat) :
    Nat.fib (m + 3) * 2 ^ m ≤ Nat.fib (m + 2) * 2 ^ (m + 1) := by
  have hBound : Nat.fib (m + 3) ≤ 2 * Nat.fib (m + 2) := by
    have h1 : Nat.fib (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 1) :=
      Omega.fib_succ_succ' (m + 1)
    have h2 : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
    omega
  calc Nat.fib (m + 3) * 2 ^ m
      ≤ 2 * Nat.fib (m + 2) * 2 ^ m := Nat.mul_le_mul_right _ hBound
    _ = Nat.fib (m + 2) * 2 ^ (m + 1) := by ring

/-- F_{m+2} > 0 (projection ratio positivity).
    prop:pom-projection-ratio-positive -/
theorem projection_ratio_positive (m : Nat) : 0 < Nat.fib (m + 2) :=
  Nat.fib_pos.mpr (by omega)

/-! ### S_q positivity and Cauchy-Schwarz restatement -/

/-- S_q(m) > 0 for all q, m.
    prop:pom-sq-pos -/
theorem momentSum_pos (q m : Nat) : 0 < momentSum q m := by
  have : Nat.fib (m + 2) ≤ momentSum q m := momentSum_ge_card q m
  have : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
  omega

/-- Cauchy-Schwarz: S_2(m) · S_0(m) ≥ S_1(m)².
    prop:pom-sq-cauchy-schwarz-restated -/
theorem momentSum_cauchy_schwarz_restated (m : Nat) :
    momentSum 2 m * momentSum 0 m ≥ (momentSum 1 m) ^ 2 := by
  rw [momentSum_zero m, momentSum_one m, Nat.mul_comm]
  exact momentSum_cauchy_schwarz m

/-! ### Task B: Rényi bound wrappers -/

theorem renyi_upper_bound (q m : Nat) (hq : 1 ≤ q) :
    momentSum q m ≤ (X.maxFiberMultiplicity m) ^ (q - 1) * 2 ^ m :=
  momentSum_le_max_pow q m hq

/-- prop:pom-rq-universal-bounds-s1 -/
theorem moment_sum_one_eq_pow (m : Nat) : momentSum 1 m = 2 ^ m := momentSum_one m
/-- prop:pom-rq-universal-bounds-s0 -/
theorem moment_sum_zero_eq_card (m : Nat) : momentSum 0 m = Nat.fib (m + 2) := momentSum_zero m

/-! ### Task C: Max fiber probability bounds -/

theorem max_fiber_le_pow (m : Nat) : X.maxFiberMultiplicity m ≤ 2 ^ m := by
  -- D_m ≤ 2^m since fiber(x) ⊆ Word m and |Word m| = 2^m
  obtain ⟨x, hx⟩ := X.maxFiberMultiplicity_achieved m
  rw [← hx, X.fiberMultiplicity]
  calc (X.fiber x).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (Word m) := Finset.card_univ
    _ = 2 ^ m := X.Word_card m

/-- cor:pom-max-fiber-rate-endpoint-lower -/
theorem max_fiber_ge_one (m : Nat) : 1 ≤ X.maxFiberMultiplicity m :=
  X.maxFiberMultiplicity_pos m

/-- cor:pom-max-fiber-rate-endpoint-both -/
theorem max_fiber_prob_bounds (m : Nat) :
    1 ≤ X.maxFiberMultiplicity m ∧ X.maxFiberMultiplicity m ≤ 2 ^ m :=
  ⟨max_fiber_ge_one m, max_fiber_le_pow m⟩


/-- The number of No11 words of length m equals F_{m+2}.
    prop:no11-word-count -/
theorem no11_count (m : Nat) : Fintype.card (X m) = Nat.fib (m + 2) := X.card_eq_fib m

end

end Omega.Frontier


-- Paper: def:pi-m2-m1-golden
-- Source: sections/body/folding/subsec__folding-multiscale.tex:43
/-- For `m₂ ≥ m₁`, the restriction projection takes a stable word
to its prefix of length `m₁`. -/
def piGolden (m₂ m₁ : ℕ) (h : m₁ ≤ m₂) : Fin m₁ → Fin m₂ :=
  fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩
