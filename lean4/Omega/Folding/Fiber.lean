import Omega.Folding.Fold

namespace Omega

namespace X

noncomputable section

/-- The finite preimage of a stable word under `Fold`.
    def:fold-fiber -/
def fiber (x : X m) : Finset (Word m) := by
  classical
  exact Finset.univ.filter fun w => Fold w = x

@[simp] theorem mem_fiber {x : X m} {w : Word m} :
    w ∈ fiber x ↔ Fold w = x := by
  classical
  simp [fiber]

@[simp] theorem self_mem_fiber (x : X m) : x.1 ∈ fiber x := by
  classical
  simp [fiber]

/-- cor:fold-fiber-nonempty -/
theorem fiber_nonempty (x : X m) : (fiber x).Nonempty :=
  ⟨x.1, self_mem_fiber x⟩

theorem fiber_card_pos (x : X m) : 0 < (fiber x).card := by
  classical
  exact Finset.card_pos.mpr (fiber_nonempty x)

/-- A canonical preimage of a stable word, obtained by viewing it as a raw word. -/
def choosePreimage (x : X m) : Word m :=
  x.1

@[simp] theorem Fold_choosePreimage (x : X m) : Fold (choosePreimage x) = x :=
  Fold_stable x

@[simp] theorem choosePreimage_mem_fiber (x : X m) : choosePreimage x ∈ fiber x := by
  classical
  simp [choosePreimage]

@[simp] theorem mem_fiber_Fold (w : Word m) : w ∈ fiber (Fold w) := by
  classical
  simp [fiber]

/-- Witness-carrying elements of the finite fiber over `x`. -/
abbrev FiberElem (x : X m) := {w : Word m // w ∈ fiber x}

/-- A proof-oriented version of the fiber using the equation `Fold w = x`. -/
abbrev FiberPoint (x : X m) := {w : Word m // Fold w = x}

noncomputable def fiberElemEquivSubtype (x : X m) : FiberElem x ≃ ↥(fiber x) where
  toFun w := ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by
    cases w
    rfl
  right_inv w := by
    cases w
    rfl

noncomputable def fiberElemEquivFiberPoint (x : X m) : FiberElem x ≃ FiberPoint x where
  toFun w := ⟨w.1, (mem_fiber).1 w.2⟩
  invFun w := ⟨w.1, (mem_fiber).2 w.2⟩
  left_inv w := by
    cases w
    rfl
  right_inv w := by
    cases w
    rfl

/-- Noncomputable ranking of a fiber element by its position in `Fin card`.
    def:fold-fiber-rank -/
noncomputable def rank (x : X m) : FiberElem x ≃ Fin (fiber x).card :=
  (fiberElemEquivSubtype x).trans <|
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])

/-- Noncomputable unranking map for a fiber.
    def:fold-fiber-unrank -/
noncomputable def unrank (x : X m) : Fin (fiber x).card → FiberElem x :=
  (rank x).symm

/-- cor:fold-fiber-rank-unrank -/
@[simp] theorem rank_unrank (x : X m) (i : Fin (fiber x).card) :
    rank x (unrank x i) = i := by
  simp [rank, unrank]

@[simp] theorem unrank_rank (x : X m) (w : FiberElem x) :
    unrank x (rank x w) = w := by
  simp [rank, unrank]

/-- The raw word returned by unranking a fiber index. -/
noncomputable def unrankWord (x : X m) (i : Fin (fiber x).card) : Word m :=
  (unrank x i).1

@[simp] theorem unrankWord_mem_fiber (x : X m) (i : Fin (fiber x).card) :
    unrankWord x i ∈ fiber x :=
  (unrank x i).2

/-- cor:fold-fiber-unrank-fold -/
@[simp] theorem Fold_unrankWord (x : X m) (i : Fin (fiber x).card) :
    Fold (unrankWord x i) = x := by
  exact (mem_fiber).1 (unrankWord_mem_fiber x i)

/-- Rank a raw word once a proof is given that it lies in the fiber. -/
noncomputable def rankOfFoldEq (x : X m) (w : Word m) (h : Fold w = x) :
    Fin (fiber x).card :=
  rank x ⟨w, (mem_fiber).2 h⟩

@[simp] theorem unrankWord_rankOfFoldEq (x : X m) (w : Word m) (h : Fold w = x) :
    unrankWord x (rankOfFoldEq x w h) = w := by
  change (unrank x (rankOfFoldEq x w h)).1 = w
  have hEq : unrank x (rankOfFoldEq x w h) = ⟨w, (mem_fiber).2 h⟩ := by
    simp [rankOfFoldEq]
  exact congrArg Subtype.val hEq

@[simp] theorem rankOfFoldEq_choosePreimage (x : X m) :
    unrankWord x (rankOfFoldEq x (choosePreimage x) (Fold_choosePreimage x)) = choosePreimage x := by
  exact unrankWord_rankOfFoldEq x (choosePreimage x) (Fold_choosePreimage x)

/-- The word space has cardinality 2^m.
    thm:word-card -/
theorem Word_card (m : Nat) : Fintype.card (Word m) = 2 ^ m := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Fiber cardinalities sum to the total word count (fibers partition `Word m`).
    thm:fiber-card-sum -/
theorem fiber_card_sum (m : Nat) :
    ∑ x : X m, (fiber x).card = Fintype.card (Word m) := by
  classical
  have hDisjoint : (↑(Finset.univ : Finset (X m)) : Set (X m)).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwx hwy
    exact hxy ((mem_fiber.1 hwx).symm.trans (mem_fiber.1 hwy))
  have hUnion : (Finset.univ : Finset (Word m)) = Finset.univ.biUnion fiber := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    exact ⟨Fold w, trivial, mem_fiber_Fold w⟩
  calc ∑ x : X m, (fiber x).card
      = (Finset.univ.biUnion fiber).card := (Finset.card_biUnion hDisjoint).symm
    _ = (Finset.univ : Finset (Word m)).card := by rw [← hUnion]
    _ = Fintype.card (Word m) := Finset.card_univ

/-- Fiber cardinalities sum to 2^m.
    thm:fiber-card-sum-eq-pow -/
theorem fiber_card_sum_eq_pow (m : Nat) :
    ∑ x : X m, (fiber x).card = 2 ^ m := by
  rw [fiber_card_sum, Word_card]

/-- The stable value of a stable word is a valid Fin index. -/
def stableValueFin (x : X m) : Fin (Nat.fib (m + 2)) :=
  ⟨stableValue x, stableValue_lt_fib x⟩

/-- stableValueFin is injective. -/
theorem stableValueFin_injective (m : Nat) :
    Function.Injective (stableValueFin (m := m)) := by
  intro x y h
  have := congr_arg Fin.val h
  simp only [stableValueFin] at this
  exact (Function.HasLeftInverse.injective ⟨X.ofNat m, X.ofNat_stableValue⟩) this

/-- The stable syntax space is equivalent to Fin(F(m+2)).
    This is the core encoding result: X_m ≃ {0, ..., F_{m+2}-1}. -/
noncomputable def stableValueEquiv (m : Nat) : X m ≃ Fin (Nat.fib (m + 2)) :=
  Fintype.equivFinOfCardEq (X.card_eq_fib m)

/-- The stableValueFin map is surjective (from injectivity + matching cardinality). -/
theorem stableValueFin_surjective (m : Nat) :
    Function.Surjective (stableValueFin (m := m)) :=
  (Finite.injective_iff_surjective_of_equiv (stableValueEquiv m)).mp
    (stableValueFin_injective m)

/-- The stableValueFin map is bijective. -/
theorem stableValueFin_bijective (m : Nat) :
    Function.Bijective (stableValueFin (m := m)) :=
  ⟨stableValueFin_injective m, stableValueFin_surjective m⟩

/-- The Zeckendorf value map gives a bijection X_m ↔ Fin(F_{m+2}), proving that
    the Fibonacci quotient monoid is isomorphic to {0,...,F_{m+2}-1}.
    thm:monoid-quotient-is-N -/
theorem paper_monoid_quotient_is_N (m : Nat) :
    Function.Bijective (stableValueFin (m := m)) :=
  stableValueFin_bijective m

/-- The fiber multiplicity of a stable word x: the number of raw words folding to x. -/
def fiberMultiplicity (x : X m) : Nat := (fiber x).card

/-- Fiber multiplicity is positive for every stable word. -/
theorem fiberMultiplicity_pos (x : X m) : 0 < fiberMultiplicity x :=
  fiber_card_pos x

/-- Fiber multiplicities sum to 2^m. -/
theorem fiberMultiplicity_sum_eq_pow (m : Nat) :
    ∑ x : X m, fiberMultiplicity x = 2 ^ m :=
  fiber_card_sum_eq_pow m

/-- The average fiber multiplicity is 2^m / |X_m|.
    Since |X_m| = F_{m+2}, this ratio approaches φ^m / √5 as m grows. -/
theorem fiberMultiplicity_avg (m : Nat) :
    ∑ x : X m, fiberMultiplicity x = 2 ^ m ∧
    Fintype.card (X m) = Nat.fib (m + 2) :=
  ⟨fiberMultiplicity_sum_eq_pow m, X.card_eq_fib m⟩

/-- For n < F(m+2), ofNat m n has stable value n. -/
theorem stableValue_ofNat_lt (n : Nat) (hn : n < Nat.fib (m + 2)) :
    stableValue (X.ofNat m n) = n := by
  obtain ⟨x, hx⟩ := stableValueFin_surjective m ⟨n, hn⟩
  have hVal : stableValue x = n := by simpa [stableValueFin] using congr_arg Fin.val hx
  rw [show X.ofNat m n = x from by rw [← hVal, X.ofNat_stableValue], hVal]

/-- For n < F(m+2), ofNat and stableValue form a round-trip. -/
theorem stableValue_ofNat_mod (n : Nat) :
    stableValue (X.ofNat m (n % Nat.fib (m + 2))) = n % Nat.fib (m + 2) :=
  stableValue_ofNat_lt _ (Nat.mod_lt n (fib_succ_pos (m + 1)))


end

end X

end Omega
