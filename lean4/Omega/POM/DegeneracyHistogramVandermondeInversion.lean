import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

theorem paper_pom_degeneracy_histogram_vandermonde_inversion (D : ℕ) (N N' : Fin D → ℚ)
    (hMoments :
      ∀ q : Fin D,
        (∑ d : Fin D, N d * ((d.1 + 1 : ℚ) ^ q.1)) =
          ∑ d : Fin D, N' d * ((d.1 + 1 : ℚ) ^ q.1)) :
    N = N' := by
  have hInjective : Function.Injective (fun d : Fin D => ((d.1 + 1 : ℕ) : ℚ)) := by
    intro a b hab
    apply Fin.ext
    have hnat :
        ((((a : ℕ) + 1 : ℕ) : ℚ)) = ((((b : ℕ) + 1 : ℕ) : ℚ)) := hab
    exact Nat.succ.inj (Nat.cast_inj.mp hnat)
  have hzero :
      (fun d : Fin D => N d - N' d) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun d : Fin D => ((d.1 + 1 : ℕ) : ℚ)) (v := fun d : Fin D => N d - N' d)
      hInjective ?_
    intro q
    have hMomentQ :
        (∑ d : Fin D, N d * (((d.1 + 1 : ℕ) : ℚ) ^ q.1)) =
          ∑ d : Fin D, N' d * (((d.1 + 1 : ℕ) : ℚ) ^ q.1) := by
      simpa using hMoments q
    calc
      ∑ d : Fin D, (N d - N' d) * (((d.1 + 1 : ℕ) : ℚ) ^ q.1) =
          (∑ d : Fin D, N d * (((d.1 + 1 : ℕ) : ℚ) ^ q.1)) -
            ∑ d : Fin D, N' d * (((d.1 + 1 : ℕ) : ℚ) ^ q.1) := by
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hMomentQ, sub_self]
  ext d
  exact sub_eq_zero.mp (congrArg (fun f : Fin D → ℚ => f d) hzero)

end Omega.POM
