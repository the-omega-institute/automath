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

/-- Paper package (n=0 instance): Walsh-Parseval concrete case.
    thm:xi-hypercube-fourier-walsh-boundary-parseval -/
theorem paper_xi_hypercube_fourier_walsh_boundary_parseval_zero (f : Word 0 → ℤ) :
    ∑ I : Finset (Fin 0), walshBias f I ^ 2 =
      2 ^ 0 * ∑ w : Word 0, f w ^ 2 :=
  parseval_zero f

end Omega.Zeta.WalshParseval
