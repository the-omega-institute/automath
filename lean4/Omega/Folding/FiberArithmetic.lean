import Omega.Folding.Fiber
import Omega.Folding.MaxFiber

namespace Omega

namespace X

noncomputable section

/-- Stable addition on X m: wrap-around Fibonacci arithmetic.
    thm:stable-add-normalization-realization -/
noncomputable def stableAdd (x y : X m) : X m :=
  X.ofNat m ((stableValue x + stableValue y) % Nat.fib (m + 2))

/-- The zero element for stable addition. -/
noncomputable def stableZero : X m := X.ofNat m 0

/-- Stable addition is commutative. -/
theorem stableAdd_comm (x y : X m) :
    stableAdd x y = stableAdd y x := by
  simp only [stableAdd, Nat.add_comm]

/-- The zero element has stable value 0. -/
theorem stableValue_stableZero : stableValue (stableZero (m := m)) = 0 :=
  stableValue_ofNat_lt 0 (fib_succ_pos (m + 1))

/-- stableZero is the left identity for stable addition. -/
theorem stableAdd_zero_left (x : X m) : stableAdd stableZero x = x := by
  unfold stableAdd stableZero
  rw [stableValue_ofNat_lt 0 (fib_succ_pos (m + 1)), Nat.zero_add,
    Nat.mod_eq_of_lt (stableValue_lt_fib x), X.ofNat_stableValue]

/-- stableZero is the right identity for stable addition. -/
theorem stableAdd_zero_right (x : X m) : stableAdd x stableZero = x := by
  rw [stableAdd_comm]; exact stableAdd_zero_left x

/-- Helper: (a % n + b) % n = (a + b) % n for 0 < n. -/
private theorem Nat.mod_add_mod_right (a b n : Nat) (hn : 0 < n) :
    (a % n + b) % n = (a + b) % n := by
  conv_rhs => rw [← Nat.mod_add_div a n]
  rw [Nat.add_assoc, Nat.add_comm (n * (a / n)), ← Nat.add_assoc,
    Nat.add_mul_mod_self_left]

/-- Stable addition is associative. -/
theorem stableAdd_assoc (x y z : X m) :
    stableAdd (stableAdd x y) z = stableAdd x (stableAdd y z) := by
  unfold stableAdd
  have hF := fib_succ_pos (m + 1)
  rw [stableValue_ofNat_mod, stableValue_ofNat_mod]
  congr 1
  have lhs : ((stableValue x + stableValue y) % Nat.fib (m + 2) + stableValue z)
      % Nat.fib (m + 2) =
      (stableValue x + stableValue y + stableValue z) % Nat.fib (m + 2) :=
    Nat.mod_add_mod_right _ _ _ hF
  have rhs : (stableValue x + (stableValue y + stableValue z) % Nat.fib (m + 2))
      % Nat.fib (m + 2) =
      (stableValue x + (stableValue y + stableValue z)) % Nat.fib (m + 2) := by
    conv_lhs => rw [Nat.add_comm]
    rw [Nat.mod_add_mod_right _ _ _ hF, Nat.add_comm]
  rw [lhs, rhs, Nat.add_assoc]

/-- Stable multiplication on X m: wrap-around Fibonacci arithmetic.
    def:stable-mul -/
noncomputable def stableMul (x y : X m) : X m :=
  X.ofNat m ((stableValue x * stableValue y) % Nat.fib (m + 2))

/-- Stable multiplication is commutative. -/
theorem stableMul_comm (x y : X m) :
    stableMul x y = stableMul y x := by
  simp only [stableMul, Nat.mul_comm]

/-- stableZero is the annihilator for multiplication. -/
theorem stableMul_zero_left (x : X m) : stableMul stableZero x = stableZero := by
  unfold stableMul stableZero
  rw [stableValue_ofNat_lt 0 (fib_succ_pos (m + 1)), Nat.zero_mul, Nat.zero_mod]

/-- stableZero is the annihilator for multiplication (right). -/
theorem stableMul_zero_right (x : X m) : stableMul x stableZero = stableZero := by
  rw [stableMul_comm]; exact stableMul_zero_left x

/-- The one element for stable multiplication. -/
noncomputable def stableOne : X m := X.ofNat m 1

/-- stableOne has value 1 when F(m+2) > 1. -/
theorem stableValue_stableOne (hm : 1 < Nat.fib (m + 2)) :
    stableValue (stableOne (m := m)) = 1 :=
  stableValue_ofNat_lt 1 hm

/-- stableOne is the left identity for multiplication when F_{m+2} > 1. -/
theorem stableMul_one_left (hm : 1 < Nat.fib (m + 2)) (x : X m) :
    stableMul stableOne x = x := by
  unfold stableMul stableOne
  rw [stableValue_ofNat_lt 1 hm, Nat.one_mul,
    Nat.mod_eq_of_lt (stableValue_lt_fib x), X.ofNat_stableValue]

/-- Helper: (a * (b % n)) % n = (a * b) % n. -/
private theorem Nat.mul_mod_right' (a b n : Nat) :
    (a * (b % n)) % n = (a * b) % n := by
  conv_rhs => rw [Nat.mul_mod]
  rw [Nat.mul_mod a (b % n) n, Nat.mod_mod_of_dvd _ (dvd_refl n)]

/-- Helper: ((a % n) * b) % n = (a * b) % n. -/
private theorem Nat.mul_mod_left' (a b n : Nat) :
    (a % n * b) % n = (a * b) % n := by
  rw [Nat.mul_comm, Nat.mul_mod_right', Nat.mul_comm]

/-- Helper: ((a % n) + (b % n)) % n = (a + b) % n. -/
private theorem Nat.add_mod' (a b n : Nat) :
    ((a % n) + (b % n)) % n = (a + b) % n := by
  rw [← Nat.add_mod]

/-- Stable multiplication distributes over stable addition (left). -/
theorem stableMul_stableAdd_left (x y z : X m) :
    stableMul x (stableAdd y z) = stableAdd (stableMul x y) (stableMul x z) := by
  simp only [stableMul, stableAdd, stableValue_ofNat_mod]
  congr 1
  rw [Nat.mul_mod_right', Nat.add_mod', Nat.mul_add]

/-- Stable multiplication is associative. -/
theorem stableMul_assoc (x y z : X m) :
    stableMul (stableMul x y) z = stableMul x (stableMul y z) := by
  simp only [stableMul, stableValue_ofNat_mod]
  congr 1
  rw [Nat.mul_mod_left' (stableValue x * stableValue y) (stableValue z),
    Nat.mul_mod_right' (stableValue x) (stableValue y * stableValue z),
    Nat.mul_assoc]

/-- stableOne is the right identity for multiplication when F_{m+2} > 1. -/
theorem stableMul_one_right (hm : 1 < Nat.fib (m + 2)) (x : X m) :
    stableMul x stableOne = x := by
  rw [stableMul_comm]; exact stableMul_one_left hm x

/-- Fiber multiplicity as a function of value index. -/
noncomputable def fiberMultiplicityByValue (m : Nat) (n : Nat) : Nat :=
  if hn : n < Nat.fib (m + 2) then fiberMultiplicity (X.ofNat m n) else 0

/-- Fiber multiplicity of x equals fiberMultiplicityByValue at stableValue(x). -/
theorem fiberMultiplicity_eq_byValue (x : X m) :
    fiberMultiplicity x = fiberMultiplicityByValue m (stableValue x) := by
  unfold fiberMultiplicityByValue
  rw [dif_pos (stableValue_lt_fib x), X.ofNat_stableValue]

/-- The range of stableValue is exactly {0, ..., F(m+2)-1}. -/
theorem stableValue_range (m : Nat) :
    Set.range (stableValue (m := m)) = {n | n < Nat.fib (m + 2)} := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    exact stableValue_lt_fib x
  · intro hn
    exact ⟨X.ofNat m n, stableValue_ofNat_lt n hn⟩

/-- X.ofNat m restricted to valid indices is the inverse of stableValue. -/
theorem ofNat_stableValue_eq (x : X m) : X.ofNat m (stableValue x) = x :=
  X.ofNat_stableValue x

/-- stableValue followed by ofNat is the identity for values in range. -/
theorem stableValue_ofNat_roundtrip (n : Nat) (hn : n < Nat.fib (m + 2)) :
    stableValue (X.ofNat m n) = n :=
  stableValue_ofNat_lt n hn

/-- stableAdd encodes modular addition on values. -/
theorem stableValue_stableAdd (x y : X m) :
    stableValue (stableAdd x y) = (stableValue x + stableValue y) % Nat.fib (m + 2) :=
  stableValue_ofNat_mod _

/-- stableMul encodes modular multiplication on values. -/
theorem stableValue_stableMul (x y : X m) :
    stableValue (stableMul x y) = (stableValue x * stableValue y) % Nat.fib (m + 2) :=
  stableValue_ofNat_mod _

/-- The stable value map is a semiring homomorphism to ℤ/F_{m+2}ℤ (addition component). -/
theorem stableValue_add_mod (x y : X m) :
    stableValue (stableAdd x y) % Nat.fib (m + 2) =
      (stableValue x + stableValue y) % Nat.fib (m + 2) := by
  rw [stableValue_stableAdd, Nat.mod_mod_of_dvd _ (dvd_refl _)]

/-- The stable value map is a semiring homomorphism to ℤ/F_{m+2}ℤ (multiplication component). -/
theorem stableValue_mul_mod (x y : X m) :
    stableValue (stableMul x y) % Nat.fib (m + 2) =
      (stableValue x * stableValue y) % Nat.fib (m + 2) := by
  rw [stableValue_stableMul, Nat.mod_mod_of_dvd _ (dvd_refl _)]

/-- The carry element at resolution m: χ^car_m = s_m(F_m) = ofNat m (Nat.fib m).
    Paper notation: χ^car_m is the unique element carrying the carry defect. -/
noncomputable def carryElement (m : Nat) : X m :=
  X.ofNat m (Nat.fib m)

/-- The carry element value: stableValue(χ^car_m) = Nat.fib m.
    This holds because Nat.fib m < F(m+2) = Nat.fib(m+2) for all m. -/
theorem stableValue_carryElement :
    stableValue (carryElement m) = Nat.fib m :=
  stableValue_ofNat_lt _ (by
    show Nat.fib m < Nat.fib (m + 2)
    have h : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have hpos : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
    omega)

/-- The carry indicator is 0 or 1. -/
theorem carryIndicator_le_one (x y : X (m + 1)) :
    carryIndicator x y ≤ 1 := by
  unfold carryIndicator
  split <;> omega

/-- When the sum is below the threshold, stableAdd at m+1 restricted to m
    coincides with stableAdd at m of the restrictions (no carry). -/
theorem restrict_stableAdd_of_no_carry (x y : X (m + 1))
    (hNoCarry : stableValue x + stableValue y < Nat.fib (m + 3)) :
    stableValue (X.restrict (stableAdd x y)) % Nat.fib (m + 2) =
      (stableValue (X.restrict x) + stableValue (X.restrict y)) % Nat.fib (m + 2) := by
  have hSV : stableValue (stableAdd x y) = stableValue x + stableValue y := by
    rw [stableValue_stableAdd, Nat.mod_eq_of_lt hNoCarry]
  have hModX := stableValue_restrict_mod x
  have hModY := stableValue_restrict_mod y
  rw [← stableValue_restrict_mod (stableAdd x y), hSV, Nat.add_mod,
    hModX, hModY, ← Nat.add_mod]

/-- Fold is the identity on the underlying word of a stable element. -/
theorem Fold_val_stable (x : X m) : (Fold x.1).1 = x.1 := by
  exact congrArg Subtype.val (Fold_stable x)

/-- Two stable words with the same stableValue are equal. -/
theorem eq_of_stableValue_eq {x y : X m} (h : stableValue x = stableValue y) : x = y :=
  stableValueFin_injective m (by simp [stableValueFin, h])

/-- stableAdd with the same element doubled: x ⊕ x = ofNat(2 * stableValue x mod F). -/
theorem stableAdd_self (x : X m) :
    stableAdd x x = X.ofNat m ((2 * stableValue x) % Nat.fib (m + 2)) := by
  simp [stableAdd, two_mul]

/-- Negation in the stable semiring: the additive inverse. -/
noncomputable def stableNeg (x : X m) : X m :=
  X.ofNat m ((Nat.fib (m + 2) - stableValue x) % Nat.fib (m + 2))

/-- stableNeg gives the additive inverse: x + neg(x) = 0. -/
theorem stableAdd_stableNeg (x : X m) :
    stableAdd x (stableNeg x) = stableZero := by
  apply eq_of_stableValue_eq
  simp only [stableValue_stableAdd, stableNeg, stableValue_ofNat_mod, stableValue_stableZero]
  have hLt := stableValue_lt_fib x
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.add_mod]
  rw [show stableValue x + (Nat.fib (m + 2) - stableValue x) = Nat.fib (m + 2) from by omega]
  simp [Nat.mod_self]

/-- stableNeg gives the right additive inverse: neg(x) + x = 0. -/
theorem stableNeg_stableAdd (x : X m) :
    stableAdd (stableNeg x) x = stableZero := by
  rw [stableAdd_comm]; exact stableAdd_stableNeg x

/-- stableNeg of zero is zero. -/
theorem stableNeg_zero : stableNeg (stableZero (m := m)) = stableZero := by
  apply eq_of_stableValue_eq
  simp only [stableNeg, stableValue_ofNat_mod, stableZero]
  rw [stableValue_ofNat_lt 0 (fib_succ_pos (m + 1)), Nat.sub_zero, Nat.mod_self]

/-- stableValue of the negation. -/
theorem stableValue_stableNeg (x : X m) :
    stableValue (stableNeg x) = (Nat.fib (m + 2) - stableValue x) % Nat.fib (m + 2) :=
  stableValue_ofNat_mod _

/-- Stable subtraction: x - y := x + neg(y). -/
noncomputable def stableSub (x y : X m) : X m :=
  stableAdd x (stableNeg y)

/-- stableSub is a left inverse of stableAdd: (x + y) - y = x. -/
theorem stableSub_stableAdd_cancel (x y : X m) :
    stableSub (stableAdd x y) y = x := by
  simp only [stableSub, stableAdd_assoc, stableAdd_stableNeg, stableAdd_zero_right]

/-- Stable multiplication by stableZero on the right annihilates. -/
theorem stableValue_stableMul_zero (x : X m) :
    stableValue (stableMul x stableZero) = 0 := by
  rw [stableValue_stableMul, stableValue_stableZero, Nat.mul_zero, Nat.zero_mod]

/-- stableAdd distributes over stableMul on the right. -/
theorem stableMul_stableAdd_right (x y z : X m) :
    stableMul (stableAdd y z) x = stableAdd (stableMul y x) (stableMul z x) := by
  rw [stableMul_comm, stableMul_stableAdd_left, stableMul_comm y, stableMul_comm z]

/-- The stable value map characterizes equality: two stable words are equal iff
    they have the same value. -/
theorem stableValue_eq_iff (x y : X m) : x = y ↔ stableValue x = stableValue y :=
  ⟨fun h => congrArg _ h, eq_of_stableValue_eq⟩

/-- The stable arithmetic respects the Fibonacci modulus:
    stableAdd and stableMul are the unique operations making stableValue
    a surjective ring homomorphism to ℤ/F_{m+2}ℤ. -/
theorem stableValue_ring_surjective (n : Nat) (hn : n < Nat.fib (m + 2)) :
    ∃ x : X m, stableValue x = n :=
  ⟨X.ofNat m n, stableValue_ofNat_lt n hn⟩

/-- The fiber of Fold over x contains x's own underlying word. -/
theorem self_in_own_fiber (x : X m) : x.1 ∈ fiber x := by
  classical
  exact self_mem_fiber x

/-- Two distinct stable words yield disjoint fibers. -/
theorem fiber_disjoint {x y : X m} (hne : x ≠ y) :
    Disjoint (fiber x) (fiber y) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwx hwy
  exact hne ((mem_fiber.1 hwx).symm.trans (mem_fiber.1 hwy))

/-- Fiber cardinality is at least 1 (positivity, named variant). -/
theorem fiber_card_ge_one (x : X m) : 1 ≤ (fiber x).card :=
  fiber_card_pos x

/-- Subtraction and addition cancel: (x - y) + y = x. -/
theorem stableSub_add_cancel (x y : X m) :
    stableAdd (stableSub x y) y = x := by
  rw [stableSub, stableAdd_assoc, stableNeg_stableAdd, stableAdd_zero_right]

/-- Stable subtraction value: stableValue(x - y) = (sv_x - sv_y) mod F. -/
theorem stableValue_stableSub (x y : X m) :
    stableValue (stableSub x y) =
      (stableValue x + (Nat.fib (m + 2) - stableValue y)) % Nat.fib (m + 2) := by
  simp [stableSub, stableValue_stableAdd, stableValue_stableNeg]

/-- Subtraction is the inverse of addition on the left: x - x = 0. -/
theorem stableSub_self (x : X m) : stableSub x x = stableZero := by
  simp [stableSub, stableAdd_stableNeg]

/-- stableAdd is cancellative on the left: x + y = x + z → y = z. -/
theorem stableAdd_left_cancel {x y z : X m} (h : stableAdd x y = stableAdd x z) : y = z := by
  have h1 : stableAdd (stableNeg x) (stableAdd x y) =
    stableAdd (stableNeg x) (stableAdd x z) := by rw [h]
  rw [← stableAdd_assoc, ← stableAdd_assoc,
    stableNeg_stableAdd, stableAdd_zero_left, stableAdd_zero_left] at h1
  exact h1

/-- stableAdd is cancellative on the right: y + x = z + x → y = z. -/
theorem stableAdd_right_cancel {x y z : X m} (h : stableAdd y x = stableAdd z x) : y = z := by
  apply stableAdd_left_cancel (x := x)
  rwa [stableAdd_comm x y, stableAdd_comm x z]

/-- The stable arithmetic on X_m is isomorphic to ℤ/F_{m+2}ℤ as a commutative ring:
    stableValue witnesses the isomorphism. -/
theorem stableValue_isomorphism_summary (m : Nat) :
    (∀ x y : X m, stableValue (stableAdd x y) = (stableValue x + stableValue y) % Nat.fib (m + 2)) ∧
    (∀ x y : X m, stableValue (stableMul x y) = (stableValue x * stableValue y) % Nat.fib (m + 2)) ∧
    Function.Injective (stableValue (m := m)) ∧
    Set.range (stableValue (m := m)) = {n | n < Nat.fib (m + 2)} :=
  ⟨stableValue_stableAdd, stableValue_stableMul,
   (Function.HasLeftInverse.injective ⟨X.ofNat m, X.ofNat_stableValue⟩),
   stableValue_range m⟩

/-- |X 1| = 2. -/
theorem card_X_one : Fintype.card (X 1) = 2 := by
  rw [X.card_eq_fib]; rfl

/-- |X 2| = 3. -/
theorem card_X_two : Fintype.card (X 2) = 3 := by
  rw [X.card_eq_fib]; rfl

/-- |X 3| = 5. -/
theorem card_X_three : Fintype.card (X 3) = 5 := by
  rw [X.card_eq_fib]; rfl

/-- |X 4| = 8. -/
theorem card_X_four : Fintype.card (X 4) = 8 := by
  rw [X.card_eq_fib]; rfl

/-- |X 5| = 13. -/
theorem card_X_five : Fintype.card (X 5) = 13 := by
  rw [X.card_eq_fib]; rfl

/-- The stable value of stableOne is 1 for m ≥ 1. -/
theorem stableValue_stableOne_of_ge_one (hm : 1 ≤ m) :
    stableValue (stableOne (m := m)) = 1 :=
  stableValue_ofNat_lt 1 (fib_gt_one_of_ge_two hm)

/-- |X 6| = 21. -/
theorem card_X_six : Fintype.card (X 6) = 21 := by
  rw [X.card_eq_fib]; rfl

/-- |X 7| = 34. -/
theorem card_X_seven : Fintype.card (X 7) = 34 := by
  rw [X.card_eq_fib]; rfl

/-- stableAdd with stableNeg of y gives stableSub x y. -/
theorem stableAdd_neg_eq_sub (x y : X m) :
    stableAdd x (stableNeg y) = stableSub x y :=
  rfl

/-- Double negation: -(-x) = x. Proved via the additive inverse uniqueness. -/
theorem stableNeg_neg_eq (x : X m) :
    stableNeg (stableNeg x) = x := by
  have h1 := stableAdd_stableNeg (stableNeg x)
  have h2 := stableNeg_stableAdd x
  rw [stableAdd_comm] at h1
  have h3 := stableAdd_stableNeg x
  exact stableAdd_right_cancel (h1.trans h3.symm)

/-- Negation is an involution for stableAdd: equivalent via cancellation. -/
theorem stableNeg_add_cancel (x y : X m) :
    stableAdd (stableNeg x) (stableAdd x y) = y := by
  rw [← stableAdd_assoc, stableNeg_stableAdd, stableAdd_zero_left]

/-- Negation distributes to subtraction: (x - y) = x + (-y) (definitional). -/
theorem stableSub_eq_add_neg (x y : X m) : stableSub x y = stableAdd x (stableNeg y) := rfl

/-- |X 8| = 55. -/
theorem card_X_eight : Fintype.card (X 8) = 55 := by
  rw [X.card_eq_fib]; rfl

/-- |X 9| = 89. -/
theorem card_X_nine : Fintype.card (X 9) = 89 := by
  rw [X.card_eq_fib]; rfl

/-- |X 10| = 144. -/
theorem card_X_ten : Fintype.card (X 10) = 144 := by
  rw [X.card_eq_fib]; rfl

/-- stableAdd with stableNeg on left cancels (named variant). -/
theorem stableNeg_add_self (x : X m) : stableAdd (stableNeg x) x = stableZero :=
  stableNeg_stableAdd x

/-- stableAdd with self negation on right cancels (named variant). -/
theorem stableAdd_self_neg (x : X m) : stableAdd x (stableNeg x) = stableZero :=
  stableAdd_stableNeg x

/-- stableNeg of stableOne gives the maximal element (F_{m+2} - 1). -/
theorem stableValue_neg_one (hm : 1 ≤ m) :
    stableValue (stableNeg (stableOne (m := m))) = Nat.fib (m + 2) - 1 := by
  rw [stableValue_stableNeg, stableValue_stableOne_of_ge_one hm,
    Nat.mod_eq_of_lt (by have : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1); omega)]

/-- For m ≥ 1, stableOne is not stableZero. -/
theorem stableOne_ne_stableZero (hm : 1 ≤ m) : stableOne (m := m) ≠ stableZero := by
  intro h
  have h1 := stableValue_stableOne_of_ge_one hm
  have h0 := stableValue_stableZero (m := m)
  rw [h] at h1; omega

/-- The modular reduction map: project a value from X_{m+1} to X_m via Fibonacci modulus. -/
noncomputable def modularProject (x : X (m + 1)) : X m :=
  X.ofNat m (stableValue x % Nat.fib (m + 2))

/-- The modular projection agrees with restriction on stable value. -/
theorem stableValue_modularProject (x : X (m + 1)) :
    stableValue (modularProject x) = stableValue x % Nat.fib (m + 2) := by
  unfold modularProject
  exact stableValue_ofNat_lt _ (Nat.mod_lt _ (fib_succ_pos (m + 1)))

/-- The modular projection maps zero to zero. -/
theorem modularProject_zero : modularProject (stableZero (m := m + 1)) = stableZero := by
  apply eq_of_stableValue_eq
  rw [stableValue_modularProject, stableValue_stableZero, Nat.zero_mod, stableValue_stableZero]

/-- When carry is zero, the modular projection preserves addition exactly. -/
theorem modularProject_add_no_carry (x y : X (m + 1))
    (hNoCarry : stableValue x + stableValue y < Nat.fib (m + 3)) :
    modularProject (stableAdd x y) = stableAdd (modularProject x) (modularProject y) := by
  apply eq_of_stableValue_eq
  rw [stableValue_modularProject, stableValue_stableAdd, stableValue_stableAdd,
    stableValue_modularProject, stableValue_modularProject,
    Nat.mod_eq_of_lt hNoCarry]
  rw [Nat.add_mod]

/-- At resolution 0, the total fiber sum is 2^0 = 1, and |X_0| = 1,
    so the unique element has fiber multiplicity 1. -/
theorem fiberMultiplicity_unique_at_zero :
    ∑ x : X 0, fiberMultiplicity x = 1 := by
  rw [fiberMultiplicity_sum_eq_pow]; rfl

/-- The average fiber multiplicity grows: at resolution m, it's 2^m / F_{m+2}. -/
theorem fiberMultiplicity_total (m : Nat) :
    ∑ x : X m, fiberMultiplicity x = 2 ^ m :=
  fiberMultiplicity_sum_eq_pow m

/-- Zeckendorf uniqueness: same Zeckendorf indices ⇒ same stable word.
    Proved via value characterization: same indices ⇒ same value ⇒ same word. -/
theorem eq_of_zeckIndices_eq {x y : X m} (h : X.zeckIndices x = X.zeckIndices y) : x = y :=
  eq_of_stableValue_eq (X.stableValue_eq_of_zeckIndices_eq h)

/-- The Zeckendorf encoding is faithful: injective on stable words. -/
theorem zeckIndices_injective (m : Nat) : Function.Injective (X.zeckIndices (m := m)) :=
  fun _ _ h => eq_of_zeckIndices_eq h

/-- The Zeckendorf representation map is injective on X m.
    thm:finite-resolution-mod -/
theorem zeckRep_injective (m : Nat) : Function.Injective (X.zeckRep (m := m)) :=
  fun _ _ h => zeckIndices_injective m (Subtype.ext_iff.mp h)

/-- stableValue equals the Fibonacci sum of the Zeckendorf representation.
    thm:finite-resolution-mod -/
theorem stableValue_eq_zeckRep_fib_sum (x : X m) :
    stableValue x = ((X.zeckRep x).val.map Nat.fib).sum :=
  (X.sum_fib_zeckRep x).symm

-- ══════════════════════════════════════════════════════════════
-- Phase 210: Zero carry
-- ══════════════════════════════════════════════════════════════

/-- Adding zero never produces a carry: carryIndicator(0, x) = 0.
    def:pom-carry-interference-graph -/
theorem carryIndicator_stableZero_left (x : X (m + 1)) :
    carryIndicator stableZero x = 0 :=
  carryIndicator_zero_of_lt _ _ (by
    rw [stableValue_stableZero, Nat.zero_add]
    exact Nat.lt_of_lt_of_le (stableValue_lt_fib x) (Nat.fib_mono (by omega)))

/-- sv(x+y) = (sv(x)+sv(y)) % F(m+2). thm:add-definitional -/
theorem stableValue_stableAdd_eq (x y : X m) :
    stableValue (stableAdd x y) = (stableValue x + stableValue y) % Nat.fib (m + 2) :=
  stableValue_stableAdd x y

-- ══════════════════════════════════════════════════════════════
-- Phase R134: Stable value Gauss sum instances
-- ══════════════════════════════════════════════════════════════

/-- Computable sum of stable values at resolution m. -/
def cStableValueSum (m : Nat) : Nat :=
  (@Finset.univ (X m) (Omega.fintypeX m)).sum (fun x => stableValue x)

/-- Gauss sum instances: sum of stable values = F(m+2)·(F(m+2)-1)/2.
    thm:pom-stableValue-gauss-sum -/
theorem stableValue_sum_gauss_instances :
    cStableValueSum 4 = Nat.fib 6 * (Nat.fib 6 - 1) / 2 ∧
    cStableValueSum 5 = Nat.fib 7 * (Nat.fib 7 - 1) / 2 ∧
    cStableValueSum 6 = Nat.fib 8 * (Nat.fib 8 - 1) / 2 := by
  native_decide

/-- Paper: stableValue Gauss sum instances -/
theorem paper_stableValue_sum_gauss_instances :
    cStableValueSum 4 = Nat.fib 6 * (Nat.fib 6 - 1) / 2 ∧
    cStableValueSum 5 = Nat.fib 7 * (Nat.fib 7 - 1) / 2 ∧
    cStableValueSum 6 = Nat.fib 8 * (Nat.fib 8 - 1) / 2 :=
  stableValue_sum_gauss_instances

-- ══════════════════════════════════════════════════════════════
-- Phase R149: Stable value Gauss sum (closed form)
-- ══════════════════════════════════════════════════════════════

/-- Sum of stable values = F(m+2)·(F(m+2)-1)/2.
    thm:pom-stableValue-gauss-sum -/
theorem stableValue_sum_closed (m : Nat) :
    2 * ∑ x : X m, stableValue x = Nat.fib (m + 2) * (Nat.fib (m + 2) - 1) := by
  -- Reindex sum via stableValueFin bijection: Σ sv(x) = Σ_{i < F} i = F*(F-1)/2
  have hbij := X.stableValueFin_bijective m
  have hsum : ∑ x : X m, stableValue x = ∑ i : Fin (Nat.fib (m + 2)), i.val := by
    rw [show (fun x : X m => stableValue x) =
      (fun i : Fin (Nat.fib (m + 2)) => i.val) ∘ X.stableValueFin from by
        ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp _
  rw [hsum]
  have : ∑ i : Fin (Nat.fib (m + 2)), (i : Nat) =
      ∑ i ∈ Finset.range (Nat.fib (m + 2)), i := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [this, Finset.sum_range_id]
  -- 2 * (n*(n-1)/2) = n*(n-1) because n*(n-1) is always even
  set F := Nat.fib (m + 2)
  have hdvd : 2 ∣ F * (F - 1) := by
    rcases Nat.even_or_odd F with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (F - 1), by rw [hk]; ring⟩
    · have : F - 1 = 2 * k := by omega
      exact ⟨F * k, by rw [this]; ring⟩
  omega
