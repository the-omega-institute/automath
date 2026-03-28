import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega

noncomputable section

/-- Fibonacci radius parameter appearing in the circle-dimension phase gate.
    con:cdim-fibonacci-radius-time-conjugacy -/
def fibRadius (m : ℕ) : ℝ :=
  (Nat.fib m : ℝ) / (Nat.fib m + 2)

/-- Poisson time parameter associated to a radius.
    con:cdim-fibonacci-radius-time-conjugacy -/
def poissonTimeOfRadius (ρ : ℝ) : ℝ :=
  2 * ρ / (1 - ρ)

/-- For the Poisson radius parametrization, the induced time equals the Fibonacci value.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem poissonTimeOf_fibRadius (m : ℕ) :
    poissonTimeOfRadius (fibRadius m) = Nat.fib m := by
  unfold poissonTimeOfRadius fibRadius
  have h : ((Nat.fib m : ℝ) + 2) ≠ 0 := by positivity
  field_simp [h]
  ring

/-- General algebraic form of `1 - ρ^2` under the Poisson radius parametrization away from the pole `t = -2`.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem one_sub_sq_of_poissonTime_param (t : ℝ) (ht : t + 2 ≠ 0) :
    1 - (t / (t + 2)) ^ 2 = 4 * (t + 1) / (t + 2) ^ 2 := by
  field_simp [ht]
  ring

/-- Algebraic identity for the squared complement of the Fibonacci radius.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem one_sub_fibRadius_sq (m : ℕ) :
    1 - (fibRadius m) ^ 2 = 4 * (Nat.fib m + 1) / (Nat.fib m + 2) ^ 2 := by
  have ht : ((Nat.fib m : ℝ) + 2) ≠ 0 := by positivity
  simpa [fibRadius] using one_sub_sq_of_poissonTime_param (Nat.fib m : ℝ) ht

/-- Natural-number specialization of `one_sub_sq_of_poissonTime_param`.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem one_sub_sq_of_poissonTime_param_nat (n : ℕ) :
    1 - ((n : ℝ) / (n + 2)) ^ 2 = 4 * (n + 1) / (n + 2) ^ 2 := by
  have ht : ((n : ℝ) + 2) ≠ 0 := by positivity
  simpa using one_sub_sq_of_poissonTime_param (n : ℝ) ht

/-- Fibonacci times factor through the additive semigroup law and commute in either order.
    con:cdim-fibonacci-poisson-semigroup-factorization -/
theorem fib_semigroup_factorization
    {α : Type*}
    (T : ℕ → α → α)
    (h_add : ∀ a b, T (a + b) = Function.comp (T a) (T b))
    (h_comm : ∀ a b, Function.comp (T a) (T b) = Function.comp (T b) (T a))
    (m : ℕ) :
    T (Nat.fib (m + 2)) = Function.comp (T (Nat.fib (m + 1))) (T (Nat.fib m)) ∧
    T (Nat.fib (m + 2)) = Function.comp (T (Nat.fib m)) (T (Nat.fib (m + 1))) := by
  have hfib : Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m := fib_succ_succ' m
  constructor
  · rw [hfib, h_add]
  · rw [hfib, h_add]
    exact h_comm _ _

/-- Right-handed Fibonacci semigroup factorization obtained from the left factorization and commutativity.
    con:cdim-fibonacci-poisson-semigroup-factorization -/
theorem fib_semigroup_factorization_right
    {α : Type*}
    (T : ℕ → α → α)
    (h_left : ∀ m,
      T (Nat.fib (m + 2)) = Function.comp (T (Nat.fib (m + 1))) (T (Nat.fib m)))
    (h_comm : ∀ a b, Function.Commute (T a) (T b))
    (m : ℕ) :
    T (Nat.fib (m + 2)) = Function.comp (T (Nat.fib m)) (T (Nat.fib (m + 1))) := by
  rw [h_left m]
  funext x
  exact h_comm _ _ x

/-- Independent right-handed Fibonacci semigroup factorization from the additive law and pairwise commutativity.
    con:cdim-fibonacci-poisson-semigroup-factorization -/
theorem fib_semigroup_factorization_right'
    {α : Type*}
    (T : ℕ → α → α)
    (h_add : ∀ a b, T (a + b) = Function.comp (T a) (T b))
    (h_comm : ∀ a b, Function.Commute (T a) (T b))
    (m : ℕ) :
    T (Nat.fib (m + 2)) = Function.comp (T (Nat.fib m)) (T (Nat.fib (m + 1))) := by
  exact fib_semigroup_factorization_right T
    (fun k => (fib_semigroup_factorization T h_add (fun a b => funext (h_comm a b)) k).1)
    h_comm m

/-- The fiber of a group homomorphism over a target point. -/
def fiberAt {G H : Type*} [Group G] [Group H] (π : G →* H) (t : H) :=
  {g : G // π g = t}

/-- Any two points in the same fiber differ by a unique kernel element on the right. -/
theorem fiber_torsor_by_kernel
    {G H : Type*} [Group G] [Group H]
    (π : G →* H) (t : H) :
    ∀ x y : fiberAt π t,
      ∃! k : π.ker, y.1 = x.1 * k.1 := by
  intro x y
  refine ⟨⟨x.1⁻¹ * y.1, ?_⟩, ?_, ?_⟩
  · change π (x.1⁻¹ * y.1) = 1
    rw [map_mul, map_inv, x.2, y.2]
    simp
  · calc
      y.1 = 1 * y.1 := by simp
      _ = x.1 * (x.1⁻¹ * y.1) := by simp
  · intro k hk
    apply Subtype.ext
    have hk' : x.1⁻¹ * y.1 = k.1 := by
      have := congrArg (fun z : G => x.1⁻¹ * z) hk
      simpa [mul_assoc] using this
    exact hk'.symm

/-- As finite sets, `ZMod (2^N)` and length-`N` bitstrings have the same cardinality. -/
theorem zmodTwoPow_card_eq_bits (N : ℕ) :
    Fintype.card (ZMod (2 ^ N)) = Fintype.card (Fin N → Bool) := by
  rw [ZMod.card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Nonconstructive finite-set equivalence between `ZMod (2^N)` and length-`N` bitstrings.
This is an equivalence of underlying finite sets, not a group isomorphism. -/
noncomputable def zmodTwoPowBitsEquiv (N : ℕ) : ZMod (2 ^ N) ≃ (Fin N → Bool) :=
  Fintype.equivOfCardEq (zmodTwoPow_card_eq_bits N)

/-- Coordinatewise bitstring encoding on six copies. -/
noncomputable def sixZmodTwoPowBitsEquiv (N : ℕ) :
    (Fin 6 → ZMod (2 ^ N)) ≃ (Fin 6 → Fin N → Bool) where
  toFun f i := zmodTwoPowBitsEquiv N (f i)
  invFun g i := (zmodTwoPowBitsEquiv N).symm (g i)
  left_inv f := by
    funext i
    exact (zmodTwoPowBitsEquiv N).left_inv (f i)
  right_inv g := by
    funext i
    exact (zmodTwoPowBitsEquiv N).right_inv (g i)

end

end Omega
