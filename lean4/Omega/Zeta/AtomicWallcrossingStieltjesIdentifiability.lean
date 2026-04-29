import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators
open Polynomial

/-- Paper label: `cor:xi-atomic-wallcrossing-stieltjes-identifiability`. -/
theorem paper_xi_atomic_wallcrossing_stieltjes_identifiability {n : ℕ}
    (t : Fin n → ℂ) (α β : Fin n → ℂ) (ht : Function.Injective t)
    (hS : ∀ z, (∀ i, z + t i ≠ 0) →
      (∑ i, α i / (z + t i)) = (∑ i, β i / (z + t i))) :
    α = β := by
  classical
  let P : ℂ[X] :=
    ∑ i ∈ Finset.univ,
      C (α i - β i) * (∏ j ∈ Finset.univ.erase i, (X + C (t j)))
  have hP_eval_good : ∀ z : ℂ, (∀ i, z + t i ≠ 0) → P.eval z = 0 := by
    intro z hz
    have hsum0 : (∑ i : Fin n, (α i - β i) / (z + t i)) = 0 := by
      have hs := hS z hz
      calc
        (∑ i : Fin n, (α i - β i) / (z + t i))
            = ∑ i : Fin n, (α i / (z + t i) - β i / (z + t i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                rw [sub_div]
        _ = (∑ i : Fin n, α i / (z + t i)) -
              (∑ i : Fin n, β i / (z + t i)) := by
                rw [Finset.sum_sub_distrib]
        _ = 0 := by simp [hs]
    have hterm : ∀ i : Fin n,
        (α i - β i) * (∏ j ∈ Finset.univ.erase i, (z + t j)) =
          (∏ j : Fin n, (z + t j)) * ((α i - β i) / (z + t i)) := by
      intro i
      have hprod :=
        Finset.prod_erase_mul (s := Finset.univ) (f := fun j : Fin n => z + t j)
          (Finset.mem_univ i)
      calc
        (α i - β i) * (∏ j ∈ Finset.univ.erase i, (z + t j))
            = ((∏ j ∈ Finset.univ.erase i, (z + t j)) * (z + t i)) *
                ((α i - β i) / (z + t i)) := by
                field_simp [hz i]
        _ = (∏ j : Fin n, (z + t j)) * ((α i - β i) / (z + t i)) := by
                rw [hprod]
    calc
      P.eval z
          = ∑ i : Fin n, (α i - β i) * (∏ j ∈ Finset.univ.erase i, (z + t j)) := by
              simp [P, Polynomial.eval_finset_sum, Polynomial.eval_prod]
      _ = ∑ i : Fin n, (∏ j : Fin n, (z + t j)) * ((α i - β i) / (z + t i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact hterm i
      _ = (∏ j : Fin n, (z + t j)) *
            (∑ i : Fin n, (α i - β i) / (z + t i)) := by
              rw [Finset.mul_sum]
      _ = 0 := by simp [hsum0]
  have hgood_infinite : Set.Infinite {z : ℂ | ∀ i : Fin n, z + t i ≠ 0} := by
    have hbad : Set.Finite (Set.range fun i : Fin n => -t i) := Set.finite_range _
    have hgood_eq :
        {z : ℂ | ∀ i : Fin n, z + t i ≠ 0} = (Set.range fun i : Fin n => -t i)ᶜ := by
      ext z
      constructor
      · intro hz hmem
        rcases hmem with ⟨i, rfl⟩
        exact hz i (by simp)
      · intro hz i hzero
        exact hz ⟨i, (eq_neg_iff_add_eq_zero.mpr hzero).symm⟩
    rw [hgood_eq]
    exact hbad.infinite_compl
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot P
    exact hgood_infinite.mono fun z hz => hP_eval_good z hz
  funext k
  have heval : P.eval (-t k) = 0 := by rw [hPzero, eval_zero]
  have hsum_at_pole :
      (∑ i : Fin n, (α i - β i) * (∏ j ∈ Finset.univ.erase i, (-t k + t j))) =
        0 := by
    simpa [P, Polynomial.eval_finset_sum, Polynomial.eval_prod] using heval
  have hsingle :
      (∑ i : Fin n, (α i - β i) * (∏ j ∈ Finset.univ.erase i, (-t k + t j))) =
        (α k - β k) * ∏ j ∈ Finset.univ.erase k, (-t k + t j) := by
    refine Finset.sum_eq_single k ?_ ?_
    · intro i _ hik
      have hk_mem : k ∈ Finset.univ.erase i := by simp [hik.symm]
      have hprod_zero : (∏ j ∈ Finset.univ.erase i, (-t k + t j)) = 0 :=
        Finset.prod_eq_zero hk_mem (by simp)
      simp [hprod_zero]
    · intro hk_not_mem
      simp at hk_not_mem
  have hprod_ne : (∏ j ∈ Finset.univ.erase k, (-t k + t j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
    intro hzero
    have hsub : t j - t k = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using hzero
    exact hjne (ht (sub_eq_zero.mp hsub))
  have hmul :
      (α k - β k) * ∏ j ∈ Finset.univ.erase k, (-t k + t j) = 0 := by
    rwa [hsingle] at hsum_at_pole
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hprod_ne)

end Omega.Zeta
