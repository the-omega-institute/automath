import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Omega.GroupUnification.GroupJGPrimeRegisterInitialObject

namespace Omega.GroupUnification

/-- The `i`-th prime coordinate of the prime register. -/
noncomputable def groupJGPrime (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime i

lemma groupJGPrime_prime (i : ℕ) : Nat.Prime (groupJGPrime i) := by
  simp [groupJGPrime]

lemma groupJGPrime_injective : Function.Injective groupJGPrime := by
  exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective

/-- The prime-register norm is the finite prime-power product attached to the exponent vector. -/
noncomputable def groupJGPrimeNorm (r : PrimeRegisterObject) : ℕ :=
  r.prod fun i e => groupJGPrime i ^ e

lemma groupJGPrimeNorm_ne_zero (r : PrimeRegisterObject) : groupJGPrimeNorm r ≠ 0 := by
  classical
  unfold groupJGPrimeNorm
  exact Finset.prod_ne_zero_iff.mpr <| by
    intro i hi
    exact pow_ne_zero _ (groupJGPrime_prime i).ne_zero

lemma groupJGPrimeNorm_pos (r : PrimeRegisterObject) : 0 < groupJGPrimeNorm r :=
  Nat.pos_of_ne_zero (groupJGPrimeNorm_ne_zero r)

lemma groupJGPrimeNorm_add (r s : PrimeRegisterObject) :
    groupJGPrimeNorm (r + s) = groupJGPrimeNorm r * groupJGPrimeNorm s := by
  classical
  unfold groupJGPrimeNorm
  refine Finsupp.prod_add_index ?_ ?_
  · intro i hi
    simp [groupJGPrime]
  · intro i hi e₁ e₂
    simp [pow_add]

lemma groupJGPrimeNorm_factorization_apply (r : PrimeRegisterObject) (i : ℕ) :
    (groupJGPrimeNorm r).factorization (groupJGPrime i) = r i := by
  classical
  calc
    (groupJGPrimeNorm r).factorization (groupJGPrime i)
        = ∑ j ∈ r.support, (groupJGPrime j ^ r j).factorization (groupJGPrime i) := by
          simpa [groupJGPrimeNorm, Finsupp.prod] using
            (Nat.factorization_prod_apply (S := r.support) (g := fun j => groupJGPrime j ^ r j)
              (p := groupJGPrime i) (hS := by
                intro j hj
                exact pow_ne_zero _ (groupJGPrime_prime j).ne_zero))
    _ = ∑ j ∈ r.support, if j = i then r i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Nat.factorization_pow, Nat.Prime.factorization (groupJGPrime_prime j)]
          by_cases hji : j = i
          · subst hji
            simp
          · have hneq : groupJGPrime j ≠ groupJGPrime i := groupJGPrime_injective.ne hji
            simp [hneq, hji]
    _ = r i := by
          by_cases hi : i ∈ r.support
          · simp [hi]
          · have hri : r i = 0 := by
              simpa [Finsupp.mem_support_iff] using hi
            simp [hri]

theorem groupJGPrimeNorm_injective : Function.Injective groupJGPrimeNorm := by
  intro r s hrs
  apply Finsupp.ext
  intro i
  have hr := groupJGPrimeNorm_factorization_apply r i
  have hs := groupJGPrimeNorm_factorization_apply s i
  rw [hrs] at hr
  exact hr.symm.trans hs

/-- The multiplicative axis parameter attached to the ellipse family. -/
noncomputable def groupJGEllipseAxis (r : PrimeRegisterObject) : ℝ :=
  groupJGPrimeNorm r

/-- The logarithmic metric on the ellipse family. -/
noncomputable def groupJGEllipseLogMetric (r s : PrimeRegisterObject) : ℝ :=
  |Real.log (groupJGEllipseAxis r / groupJGEllipseAxis s)|

/-- The prime-register norm is an injective additive-to-multiplicative homomorphism, the induced
ellipse axis is multiplicative under register addition, and the logarithmic metric is the absolute
difference of the corresponding log-norm parameters.
    thm:group-jg-ellipse-prime-homomorphism -/
theorem paper_group_jg_ellipse_prime_homomorphism :
    Function.Injective groupJGPrimeNorm ∧
      (∀ r s : PrimeRegisterObject, groupJGPrimeNorm (r + s) = groupJGPrimeNorm r * groupJGPrimeNorm s) ∧
      (∀ r s : PrimeRegisterObject, groupJGEllipseAxis (r + s) = groupJGEllipseAxis r * groupJGEllipseAxis s) ∧
      (∀ r s : PrimeRegisterObject,
        groupJGEllipseLogMetric r s =
          |Real.log (groupJGEllipseAxis r) - Real.log (groupJGEllipseAxis s)|) := by
  refine ⟨groupJGPrimeNorm_injective, groupJGPrimeNorm_add, ?_, ?_⟩
  · intro r s
    change ((groupJGPrimeNorm (r + s) : ℕ) : ℝ) = (groupJGPrimeNorm r : ℝ) * (groupJGPrimeNorm s : ℝ)
    exact_mod_cast (groupJGPrimeNorm_add r s)
  · intro r s
    have hr : 0 < groupJGEllipseAxis r := by
      change (0 : ℝ) < (groupJGPrimeNorm r : ℝ)
      exact_mod_cast (groupJGPrimeNorm_pos r)
    have hs : 0 < groupJGEllipseAxis s := by
      change (0 : ℝ) < (groupJGPrimeNorm s : ℝ)
      exact_mod_cast (groupJGPrimeNorm_pos s)
    simpa [groupJGEllipseLogMetric] using congrArg abs (Real.log_div hr.ne' hs.ne')

end Omega.GroupUnification
