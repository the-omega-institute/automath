import Mathlib.Tactic
import Omega.Core.WalshFourier

namespace Omega.Zeta.WalshParseval

open Omega.Core Finset

/-- `n = 0` Parseval: both sides reduce to `f ()²`.
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
theorem parseval_zero (f : Word 0 → ℤ) :
    ∑ I : Finset (Fin 0), walshBias f I ^ 2 =
      2 ^ 0 * ∑ w : Word 0, f w ^ 2 := by
  -- Both Finset (Fin 0) and Word 0 are effectively singletons.
  -- Use Fintype.sum_unique via Subsingleton instances.
  have huniv_sub : Subsingleton (Word 0) :=
    ⟨fun a b => funext (fun i => Fin.elim0 i)⟩
  -- For Finset (Fin 0), we know univ = {∅}
  have hFin0_card : Fintype.card (Fin 0) = 0 := Fintype.card_fin 0
  simp only [pow_zero, one_mul]
  -- Since Word 0 is a subsingleton and Finset (Fin 0) has one element,
  -- we can manually reduce: walshBias f ∅ = f w* for the unique w*.
  have hFin0_subsing : Subsingleton (Finset (Fin 0)) := by
    refine ⟨fun s t => ?_⟩
    ext i
    exact Fin.elim0 i
  have hword0_eq : (Finset.univ : Finset (Word 0)) = {fun i => Fin.elim0 i} := by
    ext w
    constructor
    · intro _
      rw [Finset.mem_singleton]
      exact Subsingleton.elim w _
    · intro _; exact Finset.mem_univ _
  have hfinset0_eq : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
    ext s
    constructor
    · intro _
      rw [Finset.mem_singleton]
      exact Subsingleton.elim s ∅
    · intro _; exact Finset.mem_univ _
  rw [hfinset0_eq, Finset.sum_singleton]
  rw [hword0_eq]
  rw [Finset.sum_singleton]
  unfold walshBias
  rw [hword0_eq, Finset.sum_singleton]
  simp [walshChar_empty]

/-- Indicator function (integer-valued).
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
def indicatorInt {n : ℕ} (B : Finset (Word n)) (w : Word n) : ℤ :=
  if w ∈ B then 1 else 0

/-- `indicatorInt B w ^ 2 = indicatorInt B w` (value in {0, 1}).
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
theorem indicatorInt_sq_eq {n : ℕ} (B : Finset (Word n)) (w : Word n) :
    indicatorInt B w ^ 2 = indicatorInt B w := by
  unfold indicatorInt
  by_cases h : w ∈ B <;> simp [h]

/-- Sum of indicator equals cardinality.
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
theorem sum_indicatorInt {n : ℕ} (B : Finset (Word n)) :
    ∑ w : Word n, indicatorInt B w = (B.card : ℤ) := by
  unfold indicatorInt
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.univ.filter (fun w : Word n => w ∈ B)) = B := by
    ext w; simp
  rw [this]

/-- General Walsh-Parseval identity: ∑_I (walshBias f I)² = 2^n · ∑_w (f w)².
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
theorem parseval_general (n : ℕ) (f : Word n → ℤ) :
    ∑ I : Finset (Fin n), walshBias f I ^ 2 =
      (2 : ℤ) ^ n * ∑ w : Word n, f w ^ 2 := by
  classical
  -- Expand walshBias squared
  calc ∑ I : Finset (Fin n), walshBias f I ^ 2
      = ∑ I : Finset (Fin n), (∑ u : Word n, walshChar I u * f u) *
          (∑ v : Word n, walshChar I v * f v) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [sq]; rfl
    _ = ∑ I : Finset (Fin n), ∑ u : Word n, ∑ v : Word n,
          (walshChar I u * f u) * (walshChar I v * f v) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ u : Word n, ∑ v : Word n, ∑ I : Finset (Fin n),
          (walshChar I u * walshChar I v) * (f u * f v) := by
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun I _ => ?_
        ring
    _ = ∑ u : Word n, ∑ v : Word n,
          (if u = v then (2 : ℤ) ^ n else 0) * (f u * f v) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_mul, walshKernel_delta]
    _ = ∑ u : Word n, (2 : ℤ) ^ n * (f u * f u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        have : ∀ v : Word n, (if u = v then (2 : ℤ) ^ n else 0) * (f u * f v) =
            if v = u then (2 : ℤ) ^ n * (f u * f v) else 0 := by
          intro v; by_cases h : u = v <;> simp [h, eq_comm]
        simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = (2 : ℤ) ^ n * ∑ w : Word n, f w ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun w _ => ?_
        ring

/-- Paper package: Walsh-Parseval for n=0 and general n.
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
theorem paper_xi_hypercube_fourier_walsh_boundary_parseval :
    (∀ f : Word 0 → ℤ, ∑ I : Finset (Fin 0), walshBias f I ^ 2 =
      2 ^ 0 * ∑ w : Word 0, f w ^ 2) ∧
    (∀ n (f : Word n → ℤ), ∑ I : Finset (Fin n), walshBias f I ^ 2 =
      (2 : ℤ) ^ n * ∑ w : Word n, f w ^ 2) :=
  ⟨parseval_zero, parseval_general⟩

end Omega.Zeta.WalshParseval
