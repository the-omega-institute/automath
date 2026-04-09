import Mathlib.Tactic

namespace Omega.Conclusion.PrimorialAdditiveVsGodelMultiplicative

open Finset

/-- Mixed-radix (additive) encoding.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
def mixedRadixVal {T : ℕ} (p : Fin T → ℕ) (a : Fin T → ℕ) : ℕ :=
  ∑ t : Fin T, a t * ∏ j ∈ Finset.Iio t, p j

/-- Godel (multiplicative) encoding.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
def godelMul {T : ℕ} (p : Fin T → ℕ) (a : Fin T → ℕ) : ℕ :=
  ∏ t : Fin T, p t ^ (a t + 1)

/-- T=0 case: both encodings are trivially injective (domain is empty function).
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem godelMul_injective_zero (p : Fin 0 → ℕ) :
    Function.Injective (godelMul p) := by
  intro a b _
  funext i
  exact Fin.elim0 i

/-- T=0 mixed radix: trivially injective.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem mixedRadixVal_injective_zero (_p : Fin 0 → ℕ)
    (a b : Fin 0 → ℕ) : a = b := by
  funext i; exact Fin.elim0 i

/-- T=1 Godel: `p 0 ^ (a 0 + 1) = p 0 ^ (b 0 + 1) → a = b` when `p 0` prime.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem godelMul_injective_one (p : Fin 1 → ℕ) (hp : (p 0).Prime) :
    Function.Injective (godelMul p) := by
  intro a b hab
  unfold godelMul at hab
  simp only [Fin.prod_univ_one] at hab
  have hp2 : 2 ≤ p 0 := hp.two_le
  have := Nat.pow_right_injective hp2 hab
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  omega

/-- T=1 mixed radix: `a 0 * 1 = b 0 * 1 → a = b`.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem mixedRadixVal_injective_one (p : Fin 1 → ℕ)
    (a b : Fin 1 → ℕ) (heq : mixedRadixVal p a = mixedRadixVal p b) : a = b := by
  unfold mixedRadixVal at heq
  simp only [Fin.sum_univ_one] at heq
  -- After simp, heq should be: a 0 * ∏ j ∈ Iio 0, p j = b 0 * ∏ j ∈ Iio 0, p j
  -- Iio (0 : Fin 1) is empty, so ∏ = 1
  have hiio : (Finset.Iio (0 : Fin 1)) = ∅ := by
    ext x; simp [Fin.lt_def]
  rw [hiio, Finset.prod_empty] at heq
  simp at heq
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst hi; exact heq

/-- Paper package: primorial additive vs Godel multiplicative (T=0,1 instances).
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem paper_conclusion_primorial_additive_vs_godel_multiplicative_small :
    (∀ (p : Fin 0 → ℕ), Function.Injective (godelMul p)) ∧
    (∀ (p : Fin 1 → ℕ), (p 0).Prime → Function.Injective (godelMul p)) ∧
    (∀ (p : Fin 1 → ℕ) (a b : Fin 1 → ℕ),
      mixedRadixVal p a = mixedRadixVal p b → a = b) :=
  ⟨godelMul_injective_zero,
   godelMul_injective_one,
   fun p a b => mixedRadixVal_injective_one p a b⟩

end Omega.Conclusion.PrimorialAdditiveVsGodelMultiplicative
