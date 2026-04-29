import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Decode a ZMod (2^N) element to its bit vector (Fin N → Bool).
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
def zmodTwoPowToBool (N : ℕ) (a : ZMod (2^N)) : Fin N → Bool :=
  fun i => Nat.testBit a.val i.val

/-- Encode a bit vector back into ZMod (2^N).
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
def boolToZmodTwoPow (N : ℕ) (b : Fin N → Bool) : ZMod (2^N) :=
  (∑ i : Fin N, if b i then 2^i.val else 0 : ℕ)

/-- Trivial bit vector at N = 0.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem zmodTwoPowToBool_zero (a : ZMod (2^0)) :
    zmodTwoPowToBool 0 a = fun i : Fin 0 => i.elim0 := by
  funext i
  exact i.elim0

/-- Trivial encode at N = 0.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem boolToZmodTwoPow_zero (b : Fin 0 → Bool) :
    boolToZmodTwoPow 0 b = 0 := by
  unfold boolToZmodTwoPow
  simp

/-- Cardinality of the Boolean cube of dimension N.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem card_fin_bool (N : ℕ) :
    Fintype.card (Fin N → Bool) = 2^N := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Cardinality of ZMod (2^N).
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem card_zmod_two_pow (N : ℕ) :
    Fintype.card (ZMod (2^N)) = 2^N := by
  rw [ZMod.card]

/-- Paper-facing finite-truncation skeleton package.
    Full bijection round-trip deferred.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem paper_cdim_dyadic_kernel_cube_finite_skeleton :
    (∀ N : ℕ, Fintype.card (ZMod (2^N)) = Fintype.card (Fin N → Bool)) ∧
    (∀ N : ℕ, Fintype.card (ZMod (2^N)) = 2^N) ∧
    (∀ N : ℕ, Fintype.card (Fin N → Bool) = 2^N) ∧
    (∀ (a : ZMod (2^0)), zmodTwoPowToBool 0 a = fun i : Fin 0 => i.elim0) ∧
    (∀ (b : Fin 0 → Bool), boolToZmodTwoPow 0 b = 0) := by
  refine ⟨?_, card_zmod_two_pow, card_fin_bool,
          zmodTwoPowToBool_zero, boolToZmodTwoPow_zero⟩
  intro N
  rw [card_zmod_two_pow, card_fin_bool]

/-! ### R451 payback: bijection round-trip. -/

/-- The indicator sum as a `Finset.range` sum is bounded by `2^N - 1`, so is
    strictly less than `2^N`. This intermediate form is convenient for
    induction on `N`. -/
theorem indicatorSum_range_lt_two_pow (b : ℕ → Bool) (N : ℕ) :
    (∑ j ∈ Finset.range N, if b j then 2^j else 0) < 2^N := by
  have hle : (∑ j ∈ Finset.range N, if b j then 2^j else 0) ≤
             ∑ j ∈ Finset.range N, 2^j := by
    refine Finset.sum_le_sum ?_
    intro j _
    split
    · exact le_refl _
    · exact Nat.zero_le _
  have hgeom : ∑ j ∈ Finset.range N, 2^j = 2^N - 1 := by
    rw [Nat.geomSum_eq (by norm_num : 2 ≤ 2) N]; simp
  have hpos : 0 < 2^N := Nat.two_pow_pos N
  omega

/-- The indicator sum is strictly bounded by `2^N`.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem indicatorSum_lt_two_pow (N : ℕ) (b : Fin N → Bool) :
    (∑ i : Fin N, if b i then 2^i.val else 0) < 2^N := by
  let b' : ℕ → Bool := fun j => if h : j < N then b ⟨j, h⟩ else false
  have hsum : (∑ i : Fin N, if b i then 2^i.val else 0) =
              ∑ j ∈ Finset.range N, if b' j then 2^j else 0 := by
    have := Fin.sum_univ_eq_sum_range (fun k : ℕ => if b' k then 2^k else 0) N
    rw [← this]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [b', dif_pos i.isLt, Fin.eta]
  rw [hsum]
  exact indicatorSum_range_lt_two_pow b' N

/-- Value of the encoded ZMod equals the raw indicator sum.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem boolToZmodTwoPow_val (N : ℕ) (b : Fin N → Bool) :
    (boolToZmodTwoPow N b).val = ∑ i : Fin N, if b i then 2^i.val else 0 := by
  unfold boolToZmodTwoPow
  rw [ZMod.val_natCast_of_lt (indicatorSum_lt_two_pow N b)]

/-- Shift-and-mod characterization of `Nat.testBit`. -/
private theorem testBit_eq_div_mod (n i : ℕ) :
    n.testBit i = decide ((n / 2^i) % 2 = 1) := by
  induction i generalizing n with
  | zero => simp [Nat.testBit_zero]
  | succ i ih =>
    rw [Nat.testBit_add_one, ih, Nat.div_div_eq_div_mul]
    congr 2
    rw [← pow_succ', pow_succ, Nat.mul_comm]

/-- For `i < N`, testBit of (S + 2^N) at index i equals testBit of S, when
    S < 2^N. -/
private theorem testBit_add_two_pow_lt
    (S : ℕ) (N i : ℕ) (_hS : S < 2^N) (hi : i < N) :
    (S + 2^N).testBit i = S.testBit i := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod]
  congr 1
  rw [Nat.add_div_of_dvd_left (Nat.pow_dvd_pow 2 (le_of_lt hi))]
  rw [Nat.pow_div (le_of_lt hi) (by norm_num : 0 < 2)]
  -- Need: (S/2^i + 2^(N-i)) % 2 = (S/2^i) % 2
  have hNi : 0 < N - i := by omega
  have h2dvd : 2 ∣ 2^(N - i) := by
    refine ⟨2^(N - i - 1), ?_⟩
    rw [← pow_succ', show N - i - 1 + 1 = N - i from by omega]
  obtain ⟨k, hk⟩ := h2dvd
  rw [hk, Nat.add_mul_mod_self_left]

/-- TestBit of (S + 2^N) at index N is true, when S < 2^N. -/
private theorem testBit_add_two_pow_self (S N : ℕ) (hS : S < 2^N) :
    (S + 2^N).testBit N = true := by
  rw [testBit_eq_div_mod]
  have h1 : (S + 2^N) / 2^N = 1 := by
    rw [Nat.add_div_of_dvd_left (dvd_refl _)]
    rw [Nat.div_self (Nat.two_pow_pos N)]
    rw [Nat.div_eq_of_lt hS]
  rw [h1]
  decide

/-- Auxiliary: testBit of the indicator partial sum over `Finset.range`.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem testBit_indicatorSum_range (b : ℕ → Bool) :
    ∀ (N i : ℕ), i < N →
      (∑ j ∈ Finset.range N, if b j then 2^j else 0).testBit i = b i := by
  intro N
  induction N with
  | zero => intro i hi; omega
  | succ N ih =>
    intro i hi
    rw [Finset.sum_range_succ]
    have hpartial_lt := indicatorSum_range_lt_two_pow b N
    by_cases hbN : b N
    · rw [if_pos hbN]
      by_cases hiN : i = N
      · subst hiN
        rw [testBit_add_two_pow_self _ _ hpartial_lt]
        exact hbN.symm
      · have hilt : i < N := by omega
        rw [testBit_add_two_pow_lt _ _ _ hpartial_lt hilt]
        exact ih i hilt
    · rw [if_neg hbN, Nat.add_zero]
      by_cases hiN : i = N
      · subst hiN
        rw [Nat.testBit_lt_two_pow hpartial_lt]
        exact (Bool.not_eq_true _).mp hbN |>.symm
      · exact ih i (by omega)

/-- Lift the ℕ-range version to a `Finset.univ` over `Fin N`.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem testBit_indicatorSum_fin (N : ℕ) (b : Fin N → Bool) (i : Fin N) :
    (∑ j : Fin N, if b j then 2^j.val else 0).testBit i.val = b i := by
  let b' : ℕ → Bool := fun j => if h : j < N then b ⟨j, h⟩ else false
  have hsum : (∑ j : Fin N, if b j then 2^j.val else 0) =
              ∑ j ∈ Finset.range N, if b' j then 2^j else 0 := by
    have := Fin.sum_univ_eq_sum_range (fun k : ℕ => if b' k then 2^k else 0) N
    rw [← this]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [b', dif_pos j.isLt, Fin.eta]
  rw [hsum, testBit_indicatorSum_range b' N i.val i.isLt]
  simp only [b', dif_pos i.isLt, Fin.eta]

/-- Round-trip: decode ∘ encode = id.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem zmodTwoPowToBool_boolToZmodTwoPow (N : ℕ) (b : Fin N → Bool) :
    zmodTwoPowToBool N (boolToZmodTwoPow N b) = b := by
  funext i
  unfold zmodTwoPowToBool
  rw [boolToZmodTwoPow_val]
  exact testBit_indicatorSum_fin N b i

/-- A finite-set equivalence between `ZMod (2^N)` and the `N`-bit cube.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
noncomputable def zmodTwoPowBoolEquiv (N : ℕ) : ZMod (2 ^ N) ≃ (Fin N → Bool) :=
  Fintype.equivOfCardEq (by rw [card_zmod_two_pow, card_fin_bool])

/-- Flatten six `N`-bit coordinates into one `6N`-bit cube.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
noncomputable def sixBitCubeFlattenEquiv (N : ℕ) :
    (Fin 6 → Fin N → Bool) ≃ (Fin (6 * N) → Bool) :=
  (Equiv.curry (Fin 6) (Fin N) Bool).symm.trans
    (finProdFinEquiv.arrowCongr (Equiv.refl Bool))

/-- Coordinatewise version of `zmodTwoPowBoolEquiv` on six copies.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
noncomputable def sixZmodTwoPowBoolEquiv (N : ℕ) :
    ((Fin 6) → ZMod (2 ^ N)) ≃ (Fin (6 * N) → Bool) :=
  let coordwise : ((Fin 6) → ZMod (2 ^ N)) ≃ (Fin 6 → Fin N → Bool) :=
    { toFun := fun f i => zmodTwoPowBoolEquiv N (f i)
      invFun := fun g i => (zmodTwoPowBoolEquiv N).symm (g i)
      left_inv := by
        intro f
        funext i
        exact (zmodTwoPowBoolEquiv N).left_inv (f i)
      right_inv := by
        intro g
        funext i
        exact (zmodTwoPowBoolEquiv N).right_inv (g i) }
  coordwise.trans (sixBitCubeFlattenEquiv N)

/-- Paper-facing finite-level dyadic kernel cube model.
    prop:cdim-dyadic-kernel-cube-inverse-limit -/
theorem paper_cdim_dyadic_kernel_cube_inverse_limit (N : Nat) :
    Nonempty (ZMod (2 ^ N) ≃ (Fin N -> Bool)) /\
    Nonempty (((Fin 6) -> ZMod (2 ^ N)) ≃ (Fin (6 * N) -> Bool)) := by
  classical
  exact ⟨⟨zmodTwoPowBoolEquiv N⟩, ⟨sixZmodTwoPowBoolEquiv N⟩⟩

end Omega.CircleDimension
