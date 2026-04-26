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

-- ══════════════════════════════════════════════════════════════
-- Phase R30: Semiring hom rigidity (Fin r → ℕ) →+* (Fin d → ℕ)
-- ══════════════════════════════════════════════════════════════

/-- Idempotent natural numbers are 0 or 1. -/
private theorem Nat.eq_zero_or_one_of_sq_eq (n : ℕ) (h : n * n = n) : n = 0 ∨ n = 1 := by
  match n, h with
  | 0, _ => left; rfl
  | 1, _ => right; rfl
  | n + 2, h => exfalso; nlinarith

/-- The standard basis vector `e_i : Fin r → ℕ`. -/
private abbrev e (r : Nat) (i : Fin r) : Fin r → ℕ := Pi.single i 1

/-- `e_i` is idempotent under pointwise multiplication. -/
private theorem e_sq (r : Nat) (i : Fin r) : e r i * e r i = e r i := by
  ext j; simp [e, Pi.mul_apply, Pi.single_apply]

/-- `e_i · e_k = 0` when `i ≠ k`. -/
private theorem e_mul_e_of_ne (r : Nat) (i k : Fin r) (hik : i ≠ k) :
    e r i * e r k = 0 := by
  ext j; simp only [e, Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
  split
  · split <;> simp_all
  · simp

/-- `∑ e_i = 1` in `Fin r → ℕ`. -/
private theorem e_sum (r : Nat) : ∑ i : Fin r, e r i = 1 := by
  ext j; simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]

/-- Any semiring hom `(Fin r → ℕ) →+* (Fin d → ℕ)` is a coordinate projection.
    thm:cdim-nr-nd-semiring-hom-rigidity -/
theorem semiring_hom_rigidity (r d : Nat) (f : (Fin r → ℕ) →+* (Fin d → ℕ)) :
    ∃ σ : Fin d → Fin r, ∀ x : Fin r → ℕ, ∀ j : Fin d, f x j = x (σ j) := by
  -- Step 1: f(e_i) is idempotent, so f(e_i) j ∈ {0, 1}
  have hidm : ∀ i : Fin r, ∀ j : Fin d, f (e r i) j = 0 ∨ f (e r i) j = 1 := by
    intro i j
    have hsq : f (e r i) * f (e r i) = f (e r i) := by
      rw [← map_mul]; exact congr_arg f (e_sq r i)
    have := congr_fun hsq j
    simp [Pi.mul_apply] at this
    exact Nat.eq_zero_or_one_of_sq_eq _ this
  -- Step 2: orthogonality: at most one f(e_i) j = 1
  have horth : ∀ (i k : Fin r) (j : Fin d), i ≠ k →
      f (e r i) j = 1 → f (e r k) j = 0 := by
    intro i k j hik hi1
    have hzero : f (e r i) * f (e r k) = 0 := by
      rw [← map_mul, e_mul_e_of_ne r i k hik, map_zero]
    have := congr_fun hzero j
    simp [Pi.mul_apply] at this
    rcases this with h | h
    · omega
    · exact h
  -- Step 3: completeness: exactly one f(e_i) j = 1
  have hone : ∀ j : Fin d, ∃! i : Fin r, f (e r i) j = 1 := by
    intro j
    -- From ∑ e_i = 1
    have hsum : f 1 = 1 := map_one f
    have hsum' : (∑ i : Fin r, f (e r i)) j = 1 := by
      have : f (∑ i : Fin r, e r i) = ∑ i : Fin r, f (e r i) := map_sum f _ _
      rw [e_sum, map_one] at this
      exact congr_fun this.symm j
    simp [Finset.sum_apply] at hsum'
    -- Sum of {0,1}-valued things equals 1 → exactly one is 1
    have hex : ∃ i : Fin r, f (e r i) j = 1 := by
      by_contra hall
      push_neg at hall
      have : ∀ i : Fin r, f (e r i) j = 0 := by
        intro i; rcases hidm i j with h | h
        · exact h
        · exact absurd h (hall i)
      simp [this] at hsum'
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, hi, fun k hk => ?_⟩
    by_contra hne
    exact absurd (horth k i j hne hk) (by omega)
  -- Step 4: define σ
  choose σ hσ huniq using fun j => hone j
  refine ⟨σ, fun x j => ?_⟩
  -- Step 5: decompose x = ∑ x_i · e_i
  have hdecomp : x = ∑ i : Fin r, x i • e r i := by
    ext k; simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  -- f(e_i) j = 1 iff i = σ j, else 0
  have heval : ∀ i : Fin r, f (e r i) j = if i = σ j then 1 else 0 := by
    intro i
    by_cases hi : i = σ j
    · rw [if_pos hi, hi]; exact hσ j
    · rw [if_neg hi]
      rcases hidm i j with h | h
      · exact h
      · exact absurd (huniq j i h) hi
  -- Compute f(x) j = ∑ x_i · f(e_i) j = ∑ x_i · [i = σ j] = x (σ j)
  have key : ∀ i : Fin r, f (x i • e r i) j = x i * (if i = σ j then 1 else 0) := by
    intro i
    -- f(n • a) = n • f(a) for ring homs (via additivity)
    have hmap : f (x i • e r i) = x i • f (e r i) := by
      induction x i with
      | zero => simp [ map_zero]
      | succ n ih => simp [ map_add, add_smul]
    rw [hmap, Pi.smul_apply, smul_eq_mul, heval]
  calc f x j = f (∑ i : Fin r, x i • e r i) j := by rw [← hdecomp]
    _ = (∑ i : Fin r, f (x i • e r i)) j := by rw [map_sum]
    _ = ∑ i : Fin r, f (x i • e r i) j := Finset.sum_apply _ _ _
    _ = ∑ i : Fin r, x i * (if i = σ j then 1 else 0) := Finset.sum_congr rfl (fun i _ => key i)
    _ = x (σ j) := by simp [Finset.sum_ite_eq', Finset.mem_univ, mul_ite, mul_one, mul_zero]

-- ══════════════════════════════════════════════════════════════
-- Phase R32: Idempotent splitting characterization
-- ══════════════════════════════════════════════════════════════

/-- Any semiring hom from (Fin r → ℕ) maps Pi.single basis to complete orthogonal idempotents.
    prop:cdim-nr-hom-idempotent-splitting -/
theorem semiring_hom_determines_idempotents {S : Type*} [CommSemiring S]
    (r : Nat) (f : (Fin r → ℕ) →+* S) (i : Fin r) :
    f (Pi.single i 1) ^ 2 = f (Pi.single i 1) ∧
    (∀ j : Fin r, i ≠ j → f (Pi.single i 1) * f (Pi.single j 1) = 0) ∧
    ∑ k : Fin r, f (Pi.single k 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · -- Idempotency: e_i² = e_i → f(e_i)² = f(e_i)
    rw [sq, ← map_mul]
    congr 1; exact e_sq r i
  · -- Orthogonality: e_i · e_j = 0 → f(e_i) · f(e_j) = 0
    intro j hij
    rw [← map_mul, e_mul_e_of_ne r i j hij, map_zero]
  · -- Completeness: ∑ e_i = 1 → ∑ f(e_i) = 1
    rw [← map_sum, e_sum, map_one]

-- ══════════════════════════════════════════════════════════════
-- Phase R33: Aut(N^r) ≅ S_r
-- ══════════════════════════════════════════════════════════════

/-- Any semiring automorphism of (Fin r → ℕ) is a coordinate permutation.
    cor:cdim-nr-nd-semiring-hom-inj-auto -/
theorem semiring_aut_is_perm (r : Nat) (f : (Fin r → ℕ) ≃+* (Fin r → ℕ)) :
    ∃ σ : Equiv.Perm (Fin r), ∀ x : Fin r → ℕ, ∀ j : Fin r, f x j = x (σ j) := by
  obtain ⟨σ, hσ⟩ := semiring_hom_rigidity r r f.toRingHom
  -- σ is injective: if σ j₁ = σ j₂ then f.toRingHom maps Pi.single j₁ 1 and Pi.single j₂ 1
  -- to functions agreeing at all coords → f injective forces j₁ = j₂.
  have hinj : Function.Injective σ := by
    intro j₁ j₂ hσeq
    by_contra h
    -- f is surjective: take preimage of Pi.single j₁ 1
    obtain ⟨y, hy⟩ := f.surjective (Pi.single j₁ 1)
    have h1 : (f y) j₁ = 1 := by rw [hy]; simp
    have h2 : (f y) j₂ = 0 := by rw [hy]; simp [ h]
    -- But f y j₁ = y (σ j₁) and f y j₂ = y (σ j₂) = y (σ j₁)
    rw [show (f y) j₁ = f.toRingHom y j₁ from rfl, hσ y j₁] at h1
    rw [show (f y) j₂ = f.toRingHom y j₂ from rfl, hσ y j₂] at h2
    rw [← hσeq] at h2; linarith
  exact ⟨Equiv.ofBijective σ ⟨hinj, Finite.surjective_of_injective hinj⟩, hσ⟩

/-- Paper-facing wrapper for coordinate-permutation automorphism rigidity.
    cor:cdim-nr-nd-semiring-hom-inj-auto -/
theorem paper_cdim_nr_nd_semiring_hom_inj_auto (r : Nat)
    (f : (Fin r → ℕ) ≃+* (Fin r → ℕ)) :
    ∃ σ : Equiv.Perm (Fin r), ∀ x : Fin r → ℕ, ∀ j : Fin r, f x j = x (σ j) := by
  simpa using semiring_aut_is_perm r f

/-- Fibonacci radius is monotone.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem fibRadius_mono (m : Nat) : fibRadius m ≤ fibRadius (m + 1) := by
  unfold fibRadius
  have hmono : (Nat.fib m : ℝ) ≤ Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_mono (by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Fibonacci radius is strictly monotone for m ≥ 2.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem fibRadius_strict_mono (m : Nat) (hm : 2 ≤ m) : fibRadius m < fibRadius (m + 1) := by
  unfold fibRadius
  have hlt : (Nat.fib m : ℝ) < Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_lt_fib_succ (by omega)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Fibonacci radius is strictly less than 1.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem fibRadius_lt_one (m : Nat) : fibRadius m < 1 := by
  unfold fibRadius
  rw [div_lt_one (by positivity : (0 : ℝ) < (Nat.fib m : ℝ) + 2)]
  linarith

/-- Gap from 1: 1 - fibRadius(m) = 2/(F(m)+2).
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem one_sub_fibRadius (m : Nat) :
    1 - fibRadius m = 2 / (↑(Nat.fib m) + 2) := by
  unfold fibRadius
  have h : (0 : ℝ) < (Nat.fib m : ℝ) + 2 := by positivity
  field_simp
  ring

end Omega
