import Omega.Folding.FiberArithmetic
import Omega.Folding.MaxFiberTwoStep
import Omega.Folding.FiberRing
import Omega.Core.Fib

namespace Omega

namespace X

noncomputable section

/-- The ring structure on X_m: stableValue is an isomorphism to ℤ/F_{m+2}ℤ.
    Certificate: add hom + mul hom + injective + surjective + neg hom. -/
structure RingIsomorphismCertificate (m : Nat) where
  add_hom : ∀ x y : X m, stableValue (stableAdd x y) =
    (stableValue x + stableValue y) % Nat.fib (m + 2)
  mul_hom : ∀ x y : X m, stableValue (stableMul x y) =
    (stableValue x * stableValue y) % Nat.fib (m + 2)
  neg_hom : ∀ x : X m, stableValue (stableNeg x) =
    (Nat.fib (m + 2) - stableValue x) % Nat.fib (m + 2)
  injective : Function.Injective (stableValue (m := m))
  range_eq : Set.range (stableValue (m := m)) = {n | n < Nat.fib (m + 2)}

/-- The canonical ring isomorphism certificate for X_m. -/
noncomputable def ringIsoCert (m : Nat) : RingIsomorphismCertificate m where
  add_hom := stableValue_stableAdd
  mul_hom := stableValue_stableMul
  neg_hom := stableValue_stableNeg
  injective := (Function.HasLeftInverse.injective ⟨X.ofNat m, X.ofNat_stableValue⟩)
  range_eq := stableValue_range m

/-- The ring isomorphism certificate witnesses injectivity. -/
theorem ringIsoCert_injective (m : Nat) :
    Function.Injective (stableValue (m := m)) :=
  (ringIsoCert m).injective

/-- Partition X_m into even-value and odd-value elements. -/
noncomputable def evenElements (m : Nat) : Finset (X m) := by
  classical
  exact Finset.univ.filter (fun x => stableValue x % 2 = 0)

/-- Partition X_m into odd-value elements. -/
noncomputable def oddElements (m : Nat) : Finset (X m) := by
  classical
  exact Finset.univ.filter (fun x => stableValue x % 2 = 1)

/-- Even and odd elements partition X_m (disjointness). -/
theorem even_odd_disjoint (m : Nat) :
    Disjoint (evenElements m) (oddElements m) := by
  classical
  exact Finset.disjoint_filter.2 (fun x _ h1 h2 => by omega)

/-- The fiber of x consists of words whose Fold equals x,
    i.e., words whose weight equals stableValue x. -/
theorem mem_fiber_iff_fold (x : X m) (w : Word m) :
    w ∈ fiber x ↔ Fold w = x := by
  classical
  exact mem_fiber

/-- The modular projection is surjective: every element of X_m
    is the projection of some element of X_{m+1}. -/
theorem modularProject_surjective (m : Nat) :
    Function.Surjective (modularProject (m := m)) := by
  intro y
  -- y : X m. Take x = appendFalse y : X (m+1). Then restrict x = y.
  refine ⟨X.appendFalse y, ?_⟩
  apply eq_of_stableValue_eq
  rw [stableValue_modularProject, stableValue_restrict_appendFalse,
    Nat.mod_eq_of_lt (stableValue_lt_fib y)]

/-- The stable semiring has a well-defined characteristic: F(m+2). -/
theorem stableAdd_characteristic (x : X m) :
    (Finset.range (Nat.fib (m + 2))).sum (fun _ => stableValue x) % Nat.fib (m + 2) = 0 := by
  simp [Finset.sum_const, Nat.mul_mod_right]

/-- stableAdd is idempotent on zero: 0 + 0 = 0. -/
theorem stableAdd_zero_zero : stableAdd (stableZero (m := m)) stableZero = stableZero :=
  stableAdd_zero_left stableZero

/-- stableMul is idempotent on zero: 0 * 0 = 0. -/
theorem stableMul_zero_zero : stableMul (stableZero (m := m)) stableZero = stableZero :=
  stableMul_zero_left stableZero

/-- stableMul is idempotent on one (when F_{m+2} > 1): 1 * 1 = 1. -/
theorem stableMul_one_one (hm : 1 < Nat.fib (m + 2)) :
    stableMul (stableOne (m := m)) stableOne = stableOne := by
  exact stableMul_one_left hm stableOne

/-- stableAdd of x with itself n times equals stableMul by ofNat n
    (when n < F_{m+2}). This connects repeated addition to multiplication. -/
theorem stableAdd_self_eq_stableMul_two (x : X m) (hm : 2 < Nat.fib (m + 2)) :
    stableAdd x x = stableMul (X.ofNat m 2) x := by
  apply eq_of_stableValue_eq
  rw [stableValue_stableAdd, stableValue_stableMul, stableValue_ofNat_lt 2 hm]
  ring_nf


/-- The stable ring at resolution 1 has exactly 2 elements: X_1 ≅ ℤ/2ℤ. -/
theorem card_X1_eq_two : Fintype.card (X 1) = 2 := card_X_one

/-- The stable ring at resolution 2 has exactly 3 elements: X_2 ≅ ℤ/3ℤ. -/
theorem card_X2_eq_three : Fintype.card (X 2) = 3 := card_X_two

/-- stableValue is a bijection at every resolution (complete bijectivity). -/
theorem stableValue_is_bijection (m : Nat) :
    Function.Bijective (stableValueFin (m := m)) :=
  stableValueFin_bijective m

/-- The Fold map factors through stableValue: Fold w = ofNat m (weight w). -/
theorem Fold_eq_ofNat_weight (w : Word m) :
    Fold w = X.ofNat m (weight w) := rfl

/-- Two words with the same weight fold to the same stable word. -/
theorem Fold_eq_of_weight_eq {w₁ w₂ : Word m} (h : weight w₁ = weight w₂) :
    Fold w₁ = Fold w₂ := by
  simp [Fold, h]

/-- The stable value of appendFalse equals that of the original. -/
theorem stableValue_appendFalse' (x : X m) :
    stableValue (X.appendFalse x) = stableValue x :=
  stableValue_restrict_appendFalse x

/-- stableAdd with itself equals stableMul by 2 (named). -/
theorem double_is_two_mul (x : X m) (hm : 2 < Nat.fib (m + 2)) :
    stableAdd x x = stableMul (X.ofNat m 2) x :=
  stableAdd_self_eq_stableMul_two x hm

/-- The stable value of the appendTrue extension. -/
theorem stableValue_appendTrue' (x : X m) (h : get x.1 (m - 1) = false) :
    stableValue (X.appendTrue x h) = stableValue x + Nat.fib (m + 2) :=
  stableValue_appendTrue x h

/-- The stable value of the zero element at any resolution. -/
theorem stableValue_zero_eq : stableValue (stableZero (m := m)) = 0 :=
  stableValue_stableZero

/-- Fiber partition is complete: every word is in exactly one fiber. -/
theorem word_in_unique_fiber (w : Word m) :
    ∃! x : X m, w ∈ fiber x := by
  classical
  exact ⟨Fold w, mem_fiber_Fold w, fun y hy => (mem_fiber.1 hy).symm⟩

/-- The restriction of a stable word preserves stability. -/
theorem restrict_preserves_stability (x : X (m + 1)) : No11 (X.restrict x).1 :=
  (X.restrict x).2

/-- stableAdd with zero on both sides. -/
theorem stableAdd_zero_both :
    stableAdd (stableZero (m := m)) stableZero = stableZero :=
  stableAdd_zero_zero

/-- Fold is monotone in the sense that it maps to a unique stable target. -/
theorem Fold_unique_target (w : Word m) : ∃! x : X m, Fold w = x :=
  ⟨Fold w, rfl, fun _ h => h.symm⟩

/-- stableNeg is its own inverse: stableNeg ∘ stableNeg = id. -/
theorem stableNeg_involutive : Function.Involutive (stableNeg (m := m)) :=
  stableNeg_neg_eq

/-- stableNeg is injective. -/
theorem stableNeg_injective : Function.Injective (stableNeg (m := m)) :=
  stableNeg_involutive.injective

/-- stableNeg is surjective. -/
theorem stableNeg_surjective : Function.Surjective (stableNeg (m := m)) :=
  stableNeg_involutive.surjective

/-- stableNeg is bijective. -/
theorem stableNeg_bijective : Function.Bijective (stableNeg (m := m)) :=
  stableNeg_involutive.bijective

/-- stableMul by zero annihilates on the right (named). -/
theorem stableMul_annihilates_right (x : X m) :
    stableMul x stableZero = stableZero :=
  stableMul_zero_right x

/-- stableMul by zero annihilates on the left (named). -/
theorem stableMul_annihilates_left (x : X m) :
    stableMul stableZero x = stableZero :=
  stableMul_zero_left x

/-- stableAdd is injective in its second argument (fixed first). -/
theorem stableAdd_injective_right (x : X m) : Function.Injective (stableAdd x) :=
  fun _ _ h => stableAdd_left_cancel h

/-- stableAdd is injective in its first argument (fixed second). -/
theorem stableAdd_injective_left (y : X m) : Function.Injective (fun x => stableAdd x y) :=
  fun _ _ h => stableAdd_right_cancel h

/-- The stableAdd group action on X_m is free: x + · is a bijection for each x. -/
theorem stableAdd_bijective (x : X m) : Function.Bijective (stableAdd x) :=
  ⟨stableAdd_injective_right x,
   fun y => ⟨stableSub y x, by rw [stableAdd_comm]; exact stableSub_add_cancel y x⟩⟩


/-- stableSub with zero on the right: x - 0 = x. -/
theorem stableSub_zero (x : X m) : stableSub x stableZero = x := by
  rw [stableSub, stableNeg_zero, stableAdd_zero_right]

/-- stableSub with zero on the left: 0 - x = -x. -/
theorem zero_stableSub (x : X m) : stableSub stableZero x = stableNeg x := by
  rw [stableSub, stableAdd_zero_left]

/-- Fiber multiplicity of the zero element equals the number of words with weight 0. -/
theorem fiberMultiplicity_stableZero :
    fiberMultiplicity (stableZero (m := m)) ≥ 1 :=
  fiberMultiplicity_pos stableZero

/-- The Fold map is an endomorphism of Word m (in the sense that Fold : Word m → X m). -/
theorem Fold_maps_to_stable (w : Word m) : No11 (Fold w).1 :=
  (Fold w).2

/-- Stable words are bounded by all words: |X_m| ≤ |Word m| = 2^m. -/
theorem stable_le_all_words (m : Nat) :
    Fintype.card (X m) ≤ Fintype.card (Word m) :=
  Fintype.card_le_of_injective (fun x => x.1) Subtype.val_injective

/-- F_{m+2} ≤ 2^m (Fibonacci growth bound). -/
theorem fib_le_pow_two (m : Nat) : Nat.fib (m + 2) ≤ 2 ^ m := by
  rw [← X.card_eq_fib, ← Word_card]
  exact stable_le_all_words m

/-- |X_m| ≤ 2^m (combining cardinality and word space size). -/
theorem stable_card_le_pow (m : Nat) :
    Fintype.card (X m) ≤ 2 ^ m := by
  rw [← Word_card]; exact stable_le_all_words m

/-- Average fiber multiplicity: (∑ mult) / |X_m| = 2^m / F_{m+2}. -/
theorem avg_fiber_numerator_denominator (m : Nat) :
    (∑ x : X m, fiberMultiplicity x) = 2 ^ m ∧
    Fintype.card (X m) = Nat.fib (m + 2) :=
  ⟨fiberMultiplicity_sum_eq_pow m, X.card_eq_fib m⟩

/-- The modular projection preserves multiplication (no-carry case). -/
theorem modularProject_mul_no_carry (x y : X (m + 1))
    (h : stableValue x * stableValue y < Nat.fib (m + 3)) :
    modularProject (stableMul x y) = stableMul (modularProject x) (modularProject y) := by
  apply eq_of_stableValue_eq
  rw [stableValue_modularProject, stableValue_stableMul, stableValue_stableMul,
    stableValue_modularProject, stableValue_modularProject, Nat.mod_eq_of_lt h, Nat.mul_mod]

/-- stableMul by one on the right is the identity (when F > 1). -/
theorem stableMul_one_right' (hm : 1 < Nat.fib (m + 2)) (x : X m) :
    stableMul x stableOne = x := by
  rw [stableMul_comm]; exact stableMul_one_left hm x

/-- The stable ring has no zero divisors when F(m+2) is prime. -/
theorem stableMul_no_zero_divisor_of_prime (hPrime : Nat.Prime (Nat.fib (m + 2)))
    {x y : X m} (hx : x ≠ stableZero) (hy : y ≠ stableZero) :
    stableMul x y ≠ stableZero := by
  intro hxy
  have hValX : stableValue x ≠ 0 := by
    intro h; exact hx (eq_of_stableValue_eq (h.trans stableValue_stableZero.symm))
  have hValY : stableValue y ≠ 0 := by
    intro h; exact hy (eq_of_stableValue_eq (h.trans stableValue_stableZero.symm))
  have hMul := congr_arg stableValue hxy
  rw [stableValue_stableMul, stableValue_stableZero] at hMul
  have hDvd : Nat.fib (m + 2) ∣ stableValue x * stableValue y :=
    Nat.dvd_of_mod_eq_zero hMul
  rcases hPrime.dvd_mul.mp hDvd with hDvdX | hDvdY
  · exact hValX (Nat.eq_zero_of_dvd_of_lt hDvdX (stableValue_lt_fib x))
  · exact hValY (Nat.eq_zero_of_dvd_of_lt hDvdY (stableValue_lt_fib y))

/-- Concrete: F_3 = 3 is prime, so X_2 ≅ F_3 is a field. -/
theorem X2_is_integral_domain : Nat.Prime (Nat.fib 4) := by decide

/-- Concrete: F_5 = 8 is NOT prime (2^3). -/
theorem F5_not_prime : ¬ Nat.Prime (Nat.fib 6) := by decide

/-- Concrete: F_7 = 21 is NOT prime (3 × 7). -/
theorem F7_not_prime : ¬ Nat.Prime (Nat.fib 8) := by decide

/-- Concrete: F_11 = 144 is NOT prime (2^4 × 3^2). -/
theorem F11_not_prime : ¬ Nat.Prime (Nat.fib 12) := by decide

/-- Concrete: F_4 = 5 is prime. -/
theorem F4_is_prime : Nat.Prime (Nat.fib 5) := by decide

/-- Concrete: F_2 = 2 is prime. -/
theorem F2_is_prime : Nat.Prime (Nat.fib 3) := by decide

/-- F_6 = 13 is prime. -/
theorem F6_is_prime : Nat.Prime (Nat.fib 7) := by decide

/-- F_8 = 34 is NOT prime. -/
theorem F8_not_prime : ¬ Nat.Prime (Nat.fib 9) := by decide

/-- F_10 = 89 is prime. -/
theorem F10_is_prime : Nat.Prime (Nat.fib 11) := by decide

/-- The Fibonacci primes in the first 11 values: F_2=2, F_3=3, F_4=5, F_6=13, F_10=89. -/
theorem fibonacci_prime_list :
    Nat.Prime (Nat.fib 3) ∧ Nat.Prime (Nat.fib 4) ∧ Nat.Prime (Nat.fib 5) ∧
    Nat.Prime (Nat.fib 7) ∧ Nat.Prime (Nat.fib 11) :=
  ⟨F2_is_prime, X2_is_integral_domain, F4_is_prime, F6_is_prime, F10_is_prime⟩

/-- F_9 = 55 is NOT prime (5 × 11). -/
theorem F9_not_prime : ¬ Nat.Prime (Nat.fib 10) := by decide

/-- The Fibonacci composite values in F_2..F_11: F_5=8, F_7=21, F_8=34, F_9=55, F_11=144. -/
theorem fibonacci_composite_list :
    ¬ Nat.Prime (Nat.fib 6) ∧ ¬ Nat.Prime (Nat.fib 8) ∧
    ¬ Nat.Prime (Nat.fib 9) ∧ ¬ Nat.Prime (Nat.fib 10) ∧
    ¬ Nat.Prime (Nat.fib 12) :=
  ⟨F5_not_prime, F7_not_prime, F8_not_prime, F9_not_prime, F11_not_prime⟩

/-- stableValue is strictly less than 2^m (combining bounds). -/
theorem stableValue_lt_pow (x : X m) : stableValue x < 2 ^ m := by
  exact Nat.lt_of_lt_of_le (stableValue_lt_fib x) (fib_le_pow_two m)


/-- stableValue determines ofNat on valid inputs. -/
theorem ofNat_of_stableValue (x : X m) :
    X.ofNat m (stableValue x) = x :=
  X.ofNat_stableValue x

/-- Fold composed with stableValue gives back the original value. -/
theorem Fold_stableValue_roundtrip (x : X m) :
    stableValue (Fold x.1) = stableValue x := by
  rw [Fold_stable]

/-- stableAdd preserves the bound: if both < F, sum mod F < F. -/
theorem stableAdd_value_bound (x y : X m) :
    stableValue (stableAdd x y) < Nat.fib (m + 2) :=
  stableValue_lt_fib _

/-- stableMul preserves the bound. -/
theorem stableMul_value_bound (x y : X m) :
    stableValue (stableMul x y) < Nat.fib (m + 2) :=
  stableValue_lt_fib _

/-- stableNeg of stableOne gives the maximal nonzero element. -/
theorem neg_one_value (hm : 1 ≤ m) :
    stableValue (stableNeg (stableOne (m := m))) = Nat.fib (m + 2) - 1 :=
  stableValue_neg_one hm

/-- The stable ring cardinality matches the Fibonacci number. -/
theorem stable_ring_order (m : Nat) : Fintype.card (X m) = Nat.fib (m + 2) :=
  X.card_eq_fib m

/-- Concrete: |X_11| = 233. -/
theorem card_X_eleven : Fintype.card (X 11) = 233 := by
  rw [X.card_eq_fib]; rfl

/-- Concrete: |X_12| = 377. -/
theorem card_X_twelve : Fintype.card (X 12) = 377 := by
  rw [X.card_eq_fib]; rfl

/-- F_12 = 233 is prime. -/
theorem F12_is_prime : Nat.Prime (Nat.fib 13) := by native_decide

/-- |X_13| = 610. -/
theorem card_X_thirteen : Fintype.card (X 13) = 610 := by
  rw [X.card_eq_fib]; native_decide

/-- The carry element value (named variant). -/
theorem carryElement_value :
    stableValue (carryElement m) = Nat.fib m :=
  stableValue_carryElement

/-- modularProject preserves the zero element. -/
theorem modularProject_preserves_zero :
    modularProject (stableZero (m := m + 1)) = stableZero :=
  modularProject_zero

/-- stableSub value is stableAdd of x and neg y values. -/
theorem stableValue_sub_eq (x y : X m) :
    stableValue (stableSub x y) = stableValue (stableAdd x (stableNeg y)) := rfl

/-- Fiber multiplicity is always positive (named). -/
theorem fiber_always_positive (x : X m) : 0 < fiberMultiplicity x :=
  fiberMultiplicity_pos x

/-- The stable ring has exactly F_{m+2} elements (named). -/
theorem ring_cardinality (m : Nat) : Fintype.card (X m) = Nat.fib (m + 2) :=
  X.card_eq_fib m

/-- Fold preserves No11 (stable output). -/
theorem Fold_output_is_stable (w : Word m) : No11 (Fold w).1 :=
  Fold_maps_to_stable w

/-- The fiber partition is a complete disjoint decomposition. -/
theorem fiber_decomposition_complete (m : Nat) :
    (∀ w : Word m, ∃! x : X m, w ∈ fiber x) ∧
    (∀ x : X m, 0 < (fiber x).card) ∧
    (∑ x : X m, (fiber x).card = 2 ^ m) :=
  ⟨word_in_unique_fiber, fiber_card_pos, fiber_card_sum_eq_pow m⟩

/-- stableSub cancels on the right: (x + y) - y = x. -/
theorem add_sub_cancel_right (x y : X m) : stableSub (stableAdd x y) y = x :=
  stableSub_stableAdd_cancel x y

/-- stableSub followed by add recovers: (x - y) + y = x. -/
theorem sub_add_recover (x y : X m) : stableAdd (stableSub x y) y = x :=
  stableSub_add_cancel x y

/-- stableAdd homomorphism (named). -/
theorem stableAdd_hom (x y : X m) :
    stableValue (stableAdd x y) = (stableValue x + stableValue y) % Nat.fib (m + 2) :=
  stableValue_stableAdd x y

/-- stableMul homomorphism (named). -/
theorem stableMul_hom (x y : X m) :
    stableValue (stableMul x y) = (stableValue x * stableValue y) % Nat.fib (m + 2) :=
  stableValue_stableMul x y

/-- stableNeg homomorphism (named). -/
theorem stableNeg_hom (x : X m) :
    stableValue (stableNeg x) = (Nat.fib (m + 2) - stableValue x) % Nat.fib (m + 2) :=
  stableValue_stableNeg x

/-- Complete ring axioms for X_m (8 laws). -/
theorem complete_ring_axioms (m : Nat) :
    (∀ x y : X m, stableAdd x y = stableAdd y x) ∧
    (∀ x y z : X m, stableAdd (stableAdd x y) z = stableAdd x (stableAdd y z)) ∧
    (∀ x : X m, stableAdd stableZero x = x) ∧
    (∀ x : X m, stableAdd x (stableNeg x) = stableZero) ∧
    (∀ x y : X m, stableMul x y = stableMul y x) ∧
    (∀ x y z : X m, stableMul (stableMul x y) z = stableMul x (stableMul y z)) ∧
    (∀ x y z : X m, stableMul x (stableAdd y z) = stableAdd (stableMul x y) (stableMul x z)) ∧
    (∀ x y z : X m, stableAdd x y = stableAdd x z → y = z) :=
  ⟨stableAdd_comm, stableAdd_assoc, stableAdd_zero_left, stableAdd_stableNeg,
   stableMul_comm, stableMul_assoc, stableMul_stableAdd_left, fun _ _ _ h => stableAdd_left_cancel h⟩

end

/-- Even and odd stableValue elements partition X m. -/
theorem even_odd_card_sum (m : Nat) :
    (evenElements m).card + (oddElements m).card = Nat.fib (m + 2) := by
  classical
  rw [← X.card_eq_fib, ← Finset.card_univ]
  rw [← Finset.card_union_of_disjoint (even_odd_disjoint m)]
  congr 1; ext x
  simp only [Finset.mem_union, evenElements, oddElements, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Nat.mod_two_eq_zero_or_one (stableValue x) with h | h <;> simp [h]

-- ══════════════════════════════════════════════════════════════
-- Phase 116: Fold factorization + stableValue characterizations
-- ══════════════════════════════════════════════════════════════

/-- Fold factors through ofNat: Fold w = X.ofNat m (weight w). Named alias.
    prop:pom-fold-as-section -/
theorem Fold_factorization (w : Word m) : Fold w = X.ofNat m (weight w) := rfl

/-- stableValue x = 0 iff x is the all-false word.
    thm:pom-max-fiber -/
theorem stableValue_eq_zero_iff (x : X m) :
    stableValue x = 0 ↔ x = ⟨fun _ => false, no11_allFalse⟩ := by
  constructor
  · intro h; exact eq_of_stableValue_eq (h.trans stableValue_allFalse.symm)
  · intro h; rw [h]; exact stableValue_allFalse

-- ══════════════════════════════════════════════════════════════
-- Phase 119: Ring corollaries
-- ══════════════════════════════════════════════════════════════

/-- stableValue of negation: sv(-x) = (F - sv(x)) % F. -/
theorem stableValue_neg (x : X m) :
    stableValue (-x) = (Nat.fib (m + 2) - stableValue x) % Nat.fib (m + 2) :=
  stableValue_stableNeg x

/-- Fold respects addition: Fold(w1) + Fold(w2) = ofNat(m, (wt w1 + wt w2) % F).
    thm:stable-add-value-consistency -/
theorem Fold_add_weight (w1 w2 : Word m) :
    Fold w1 + Fold w2 = X.ofNat m ((weight w1 + weight w2) % Nat.fib (m + 2)) := by
  show stableAdd (Fold w1) (Fold w2) = _
  apply eq_of_stableValue_eq
  rw [stableValue_stableAdd, stableValue_ofNat_mod,
      stableValue_Fold_mod, stableValue_Fold_mod]
  simp [Nat.mod_mod, Nat.add_mod]

/-- Paper label: stableAdd definition.
    def:stable-add -/
theorem paper_stable_add_def (x y : X m) :
    stableAdd x y = X.ofNat m ((stableValue x + stableValue y) % Nat.fib (m + 2)) := by
  unfold stableAdd; rfl

/-- Paper label: Fold addition.
    cor:add-as-fold -/
theorem paper_add_as_fold (w1 w2 : Word m) :
    stableAdd (Fold w1) (Fold w2) =
    X.ofNat m ((weight w1 + weight w2) % Nat.fib (m + 2)) :=
  Fold_add_weight w1 w2

/-- Paper label: stableAdd has zero as identity.
    prop:stable-add-no-null-creation -/
theorem paper_stable_add_no_null :
    (∀ x : X m, stableAdd stableZero x = x) ∧
    (∀ x : X m, stableAdd x stableZero = x) :=
  ⟨stableAdd_zero_left, stableAdd_zero_right⟩

/-- Paper label: one fold is the normal form (idempotent).
    thm:pom-one-fold-normal-form -/
theorem paper_one_fold_normal_form (w : Word m) :
    Fold (Fold w).1 = Fold w := Fold_idempotent w

/-- Paper: Fold is idempotent + stable + surjective.
    cor:foldm-order-indep -/
theorem paper_fold_order_independent :
    (∀ w : Word m, Fold (Fold w).1 = Fold w) ∧
    (∀ w : Word m, No11 (Fold w).1) ∧
    Function.Surjective (Fold (m := m)) :=
  ⟨Fold_idempotent, fun w => (Fold w).2, Fold_surjective m⟩

/-- Truncation does not commute with Fold in general:
    there exists a word w such that Fold(truncate w) ≠ restrict(Fold w).
    Witness: w = [false, true, true] at level 3.
    prop:pom-truncation-not-commute -/
theorem paper_truncation_not_commute :
    ∃ (w : Word 3), Fold (truncate w) ≠ X.restrict (Fold w) := by
  native_decide

end X

-- ══════════════════════════════════════════════════════════════
-- Phase 242: Integer division identities
-- ══════════════════════════════════════════════════════════════

/-- Integer division: for b > 0 and any a, unique (q,r) with a = q*b + r and 0 ≤ r < b.
    thm:pom-division-section -/
theorem paper_division_section (a : ℤ) (b : ℤ) (hb : 0 < b) :
    ∃! p : ℤ × ℤ, a = p.1 * b + p.2 ∧ 0 ≤ p.2 ∧ p.2 < b := by
  refine ⟨(a / b, a % b), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- a = (a / b) * b + a % b
    have := Int.ediv_add_emod a b  -- a = b * (a / b) + a % b
    linarith
  · exact Int.emod_nonneg a (by omega)
  · exact Int.emod_lt_of_pos a hb
  · rintro ⟨q', r'⟩ ⟨heq, hr0, hrb⟩
    simp only [Prod.mk.injEq]
    have hdiv : a = (a / b) * b + a % b := by
      have := Int.ediv_add_emod a b; linarith
    have hmod_nn : 0 ≤ a % b := Int.emod_nonneg a (by omega)
    have hmod_lt : a % b < b := Int.emod_lt_of_pos a hb
    -- From heq and hdiv: q' * b + r' = (a/b) * b + a%b
    -- With 0 ≤ r' < b and 0 ≤ a%b < b, uniqueness follows
    have h1 : (q' - a / b) * b = a % b - r' := by linarith
    have h2 : |a % b - r'| < b := by
      rw [abs_lt]; constructor <;> linarith
    have h3 : q' = a / b := by
      by_contra hne
      have : |((q' - a / b) * b : ℤ)| ≥ b := by
        rw [abs_mul]
        calc |q' - a / b| * |b| ≥ 1 * |b| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              exact Int.one_le_abs (sub_ne_zero.mpr hne)
          _ = |b| := one_mul _
          _ = b := abs_of_pos hb
      rw [h1] at this; linarith
    constructor
    · exact h3
    · -- From h1 and h3: (q' - a/b) * b = 0, so a%b - r' = 0
      have h4 : a % b - r' = 0 := by rw [h3, sub_self, zero_mul] at h1; linarith
      linarith

/-- Symmetric division: for b > 0, exists (q,r) with a = q*b + r and -⌊b/2⌋ ≤ r < ⌈b/2⌉.
    cor:pom-symmetric-remainder -/
theorem paper_symmetric_remainder (a : ℤ) (b : ℤ) (hb : 0 < b) :
    ∃ q r : ℤ, a = q * b + r ∧ -(b / 2) ≤ r ∧ r < (b + 1) / 2 := by
  set r₀ := a % b with hr₀_def
  set q₀ := a / b with hq₀_def
  have hdiv : a = q₀ * b + r₀ := by
    have := Int.ediv_add_emod a b; linarith
  have hr₀_nonneg : 0 ≤ r₀ := Int.emod_nonneg a (by omega)
  have hr₀_lt : r₀ < b := Int.emod_lt_of_pos a hb
  by_cases h : r₀ < (b + 1) / 2
  · exact ⟨q₀, r₀, hdiv, by omega, h⟩
  · refine ⟨q₀ + 1, r₀ - b, ?_, ?_, ?_⟩
    · linarith
    · have : (b + 1) / 2 ≤ r₀ := by omega
      omega
    · omega

-- ══════════════════════════════════════════════════════════════
-- Phase R14: stableSucc definition and properties
-- ══════════════════════════════════════════════════════════════

namespace X

noncomputable section

/-- The successor function on X m.
    def:successor-fold -/
noncomputable def stableSucc (x : X m) : X m := stableAdd x stableOne

/-- stableValue(succ(x)) = (stableValue(x) + 1) % F_{m+2}.
    thm:successor-structure -/
theorem stableValue_stableSucc (x : X m) (hm : 1 ≤ m) :
    stableValue (stableSucc x) = (stableValue x + 1) % Nat.fib (m + 2) := by
  simp only [stableSucc, stableValue_stableAdd, stableValue_stableOne_of_ge_one hm]

/-- succ(0) = 1.
    thm:successor-structure -/
theorem stableSucc_zero (hm : 1 ≤ m) :
    stableSucc (stableZero (m := m)) = stableOne := by
  simp only [stableSucc, stableAdd_zero_left]

/-- Successor is injective.
    thm:successor-structure -/
theorem stableSucc_injective (m : Nat) :
    Function.Injective (stableSucc (m := m)) := by
  intro a b h
  exact stableAdd_right_cancel (show stableAdd a stableOne = stableAdd b stableOne from h)

-- ══════════════════════════════════════════════════════════════
-- Phase R15: stablePred + iterate successor = add
-- ══════════════════════════════════════════════════════════════

/-- The predecessor function on X m.
    def:successor-fold -/
noncomputable def stablePred (x : X m) : X m := stableSub x stableOne

/-- stableValue(pred(x)) = (stableValue(x) + F_{m+2} - 1) % F_{m+2}.
    def:successor-fold -/
theorem stableValue_stablePred (x : X m) (hm : 1 ≤ m) :
    stableValue (stablePred x) =
    (stableValue x + Nat.fib (m + 2) - 1) % Nat.fib (m + 2) := by
  rw [stablePred, stableValue_stableSub, stableValue_stableOne_of_ge_one hm]
  have hF : 1 ≤ Nat.fib (m + 2) := by have := (Nat.fib_pos (n := m + 2)).mpr (by omega); omega
  congr 1; omega

/-- pred(succ(x)) = x.
    def:successor-fold -/
theorem stablePred_stableSucc (x : X m) :
    stablePred (stableSucc x) = x := by
  simp only [stablePred, stableSucc]
  exact stableSub_stableAdd_cancel x stableOne

/-- succ(pred(x)) = x.
    def:successor-fold -/
theorem stableSucc_stablePred (x : X m) :
    stableSucc (stablePred x) = x := by
  simp only [stableSucc, stablePred]
  exact stableSub_add_cancel x stableOne

/-- Predecessor is injective.
    def:successor-fold -/
theorem stablePred_injective (m : Nat) :
    Function.Injective (stablePred (m := m)) :=
  Function.HasLeftInverse.injective ⟨stableSucc, stableSucc_stablePred⟩

/-- stableValue of n-fold successor: sv(succ^n(x)) = (sv(x) + n) % F_{m+2}.
    cor:add-from-successor -/
theorem stableValue_stableSucc_iterate (x : X m) (n : Nat) (hm : 1 ≤ m) :
    stableValue (stableSucc^[n] x) = (stableValue x + n) % Nat.fib (m + 2) := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt (stableValue_lt_fib x)]
  | succ n ih =>
    rw [Function.iterate_succ_apply', stableValue_stableSucc _ hm, ih]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.add_mod]
    ring_nf

/-- n-fold successor equals stableAdd: succ^{sv(y)}(x) = x + y.
    cor:add-from-successor -/
theorem stableSucc_iterate_eq_stableAdd (x y : X m) (hm : 1 ≤ m) :
    stableSucc^[stableValue y] x = stableAdd x y := by
  apply eq_of_stableValue_eq
  rw [stableValue_stableSucc_iterate x (stableValue y) hm, stableValue_stableAdd]

-- ══════════════════════════════════════════════════════════════
-- Phase R16: iterated add = mul + succ/pred bijective
-- ══════════════════════════════════════════════════════════════

/-- n-fold addition of x starting from zero.
    thm:mul-by-iterated-add -/
noncomputable def iteratedStableAdd (x : X m) (n : Nat) : X m :=
  (fun z => stableAdd z x)^[n] stableZero

/-- stableValue of iterated addition: sv(n·x) = (n * sv(x)) % F.
    thm:mul-by-iterated-add -/
theorem stableValue_iteratedStableAdd (x : X m) (n : Nat) :
    stableValue (iteratedStableAdd x n) =
    (n * stableValue x) % Nat.fib (m + 2) := by
  induction n with
  | zero =>
    simp only [iteratedStableAdd, Function.iterate_zero_apply, stableValue_stableZero, Nat.zero_mul,
      Nat.zero_mod]
  | succ n ih =>
    simp only [iteratedStableAdd, Function.iterate_succ_apply'] at ih ⊢
    rw [stableValue_stableAdd, ih, Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.add_mod]
    congr 1; ring

/-- Iterated addition equals multiplication: n·x via iteration = stableMul.
    thm:mul-by-iterated-add -/
theorem iteratedStableAdd_eq_stableMul (x y : X m) (hm : 1 ≤ m) :
    iteratedStableAdd x (stableValue y) = stableMul y x := by
  apply eq_of_stableValue_eq
  rw [stableValue_iteratedStableAdd, stableValue_stableMul]

/-- Successor is surjective (pred is a right inverse).
    thm:successor-structure -/
theorem stableSucc_surjective (m : Nat) :
    Function.Surjective (stableSucc (m := m)) :=
  fun y => ⟨stablePred y, stableSucc_stablePred y⟩

/-- Successor is bijective.
    thm:successor-structure -/
theorem stableSucc_bijective (m : Nat) :
    Function.Bijective (stableSucc (m := m)) :=
  ⟨stableSucc_injective m, stableSucc_surjective m⟩

/-- Predecessor is surjective (succ is a right inverse).
    thm:successor-structure -/
theorem stablePred_surjective (m : Nat) :
    Function.Surjective (stablePred (m := m)) :=
  fun y => ⟨stableSucc y, stablePred_stableSucc y⟩

/-- Predecessor is bijective.
    thm:successor-structure -/
theorem stablePred_bijective (m : Nat) :
    Function.Bijective (stablePred (m := m)) :=
  ⟨stablePred_injective m, stablePred_surjective m⟩

/-- Successor as an equivalence.
    thm:successor-structure -/
noncomputable def stableSuccEquiv (m : Nat) : X m ≃ X m :=
  Equiv.ofBijective stableSucc (stableSucc_bijective m)

end

end X

-- ══════════════════════════════════════════════════════════════
-- Phase R31: iterate composition + stableMul from successor
-- ══════════════════════════════════════════════════════════════

/-- Iterate of a sum decomposes as composition: g^[m+n] = g^[m] ∘ g^[n].
    thm:composition-two-layer -/
theorem iterate_add_comp {α : Type*} (g : α → α) (m n : Nat) :
    g^[m + n] = g^[m] ∘ g^[n] := Function.iterate_add g m n

/-- Iterate of an iterate is a single iterate with multiplied exponent.
    thm:composition-two-layer -/
theorem iterate_iterate_mul {α : Type*} (f : α → α) (m n : Nat) :
    (f^[n])^[m] = f^[m * n] := by
  rw [mul_comm]; exact (Function.iterate_mul f n m).symm

/-- Iterated addition by stableValue equals stableMul: multiplication from successor.
    thm:mul-from-successor -/
theorem stableMul_from_successor {m : Nat} (x y : X m) (hm : 1 ≤ m) :
    X.iteratedStableAdd x (stableValue y) = X.stableMul y x :=
  X.iteratedStableAdd_eq_stableMul x y hm

-- ══════════════════════════════════════════════════════════════
-- Phase R35: Cross-resolution ring homomorphism existence
-- ══════════════════════════════════════════════════════════════

/-- A unit-preserving ring hom ZMod(F_e) →+* ZMod(F_d) exists iff d ∣ e (for d,e ≥ 3).
    (→) f exists ⟹ F_d ∣ F_e (since f maps n↦n mod F_d and F_e ≡ 0) ⟹ d ∣ e by fib_dvd_iff.
    (←) d ∣ e ⟹ F_d ∣ F_e ⟹ ZMod.castHom gives the canonical quotient map.
    cor:cross-resolution-morphism-existence -/
theorem restrict_ringHom_exists_iff (d e : Nat) (hd : 3 ≤ d) (he : 3 ≤ e) :
    (∃ f : ZMod (Nat.fib e) →+* ZMod (Nat.fib d), f 1 = 1) ↔ d ∣ e := by
  constructor
  · -- (→) existence of ring hom implies d ∣ e
    rintro ⟨f, _⟩
    -- f maps (Nat.fib e : ZMod (Nat.fib e)) = 0 to f 0 = 0
    -- f also maps (Nat.fib e : ZMod (Nat.fib e)) to (Nat.fib e : ZMod (Nat.fib d)) by map_natCast
    -- So (Nat.fib e : ZMod (Nat.fib d)) = 0, hence Nat.fib d ∣ Nat.fib e
    have h1 : (Nat.fib e : ZMod (Nat.fib e)) = 0 :=
      (ZMod.natCast_eq_zero_iff (Nat.fib e) (Nat.fib e)).mpr dvd_rfl
    have h2 : f (Nat.fib e : ZMod (Nat.fib e)) = (Nat.fib e : ZMod (Nat.fib d)) :=
      map_natCast f (Nat.fib e)
    rw [h1, map_zero] at h2
    have hdvd_fib : Nat.fib d ∣ Nat.fib e :=
      (ZMod.natCast_eq_zero_iff (Nat.fib e) (Nat.fib d)).mp h2.symm
    exact (fib_dvd_iff d e hd).mp hdvd_fib
  · -- (←) d ∣ e implies existence of ring hom
    intro hde
    have hdvd_fib : Nat.fib d ∣ Nat.fib e := Nat.fib_dvd d e hde
    exact ⟨ZMod.castHom hdvd_fib (ZMod (Nat.fib d)), map_one _⟩

/-- Carry in stable addition: the quotient (sv(x)+sv(y))/F_{m+2} is at most 1.
    Since sv(x) < F and sv(y) < F, their sum < 2F, so the quotient is 0 or 1.
    thm:pom-stable-addition-carry-defect -/
theorem stableAdd_carry_binary (x y : X m) :
    (stableValue x + stableValue y) / Nat.fib (m + 2) ≤ 1 := by
  have hx := stableValue_lt_fib x
  have hy := stableValue_lt_fib y
  have hF : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
  rw [Nat.div_le_iff_le_mul hF]
  omega

/-- X_m has exactly F_{m+2} elements and characteristic F_{m+2}.
    prop:pom-fold-as-section -/
theorem X_card_eq_char (m : Nat) (hm : 1 ≤ m) :
    Fintype.card (X m) = ringChar (X m) := by
  rw [X.card_eq_fib]
  exact (ringChar.eq_iff.mpr X.instCharP).symm

end Omega
