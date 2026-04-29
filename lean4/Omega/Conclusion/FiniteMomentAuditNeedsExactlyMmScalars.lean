import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

private lemma conclusion_finite_moment_audit_needs_exactly_mm_scalars_int_split (z : Int) :
    z = (z.toNat : Int) - ((-z).toNat : Int) := by
  by_cases hz : 0 ≤ z
  · have hneg : (-z).toNat = 0 := Int.toNat_of_nonpos (by omega)
    simp [Int.toNat_of_nonneg hz, hneg]
  · have hzle : z ≤ 0 := by omega
    have hpos : 0 ≤ -z := by omega
    have hzt : z.toNat = 0 := Int.toNat_of_nonpos hzle
    simp [Int.toNat_of_nonneg hpos, hzt]

private lemma conclusion_finite_moment_audit_needs_exactly_mm_scalars_clear_den
    {ι : Type*} [Fintype ι] (x : ι → Rat) (D : Nat)
    (hden : ∀ i, (x i).den ∣ D) :
    ∀ i, ((((D / (x i).den : Nat) : Int) * (x i).num : Int) : Rat) = (D : Rat) * x i := by
  intro i
  rcases hden i with ⟨c, hc⟩
  have hden_ne : (x i).den ≠ 0 := Rat.den_nz (x i)
  have hden_pos : 0 < (x i).den := (x i).den_pos
  have hD_eq : D = c * (x i).den := by simpa [Nat.mul_comm] using hc
  have hdiv : D / (x i).den = c := by
    rw [hD_eq, Nat.mul_comm, Nat.mul_div_right _ hden_pos]
  have hdenQ : ((x i).den : Rat) ≠ 0 := by exact_mod_cast hden_ne
  rw [hdiv, hD_eq]
  calc
    ((((c : Nat) : Int) * (x i).num : Int) : Rat)
        = (c : Rat) * ((x i).num : Rat) := by norm_num
    _ = (((c * (x i).den : Nat) : Rat) * x i) := by
      norm_num
      rw [mul_assoc]
      rw [Rat.den_mul_eq_num]

/-- Paper label: `cor:conclusion-finite-moment-audit-needs-exactly-Mm-scalars`. -/
theorem paper_conclusion_finite_moment_audit_needs_exactly_mm_scalars {M r : Nat}
    (hM : 0 < M) (n : Fin r -> Nat) (hn : ∀ j, 1 <= n j)
    (hcomplete : ∀ h h' : Fin M -> Nat,
      (∀ j : Fin r,
        (∑ t : Fin M, h t * (t.1 + 1) ^ (n j)) =
          (∑ t : Fin M, h' t * (t.1 + 1) ^ (n j))) -> h = h') :
    M <= r := by
  let _ := hM
  let _ := hn
  by_contra hnot
  have hrM : r < M := Nat.lt_of_not_ge hnot
  let A : (Fin M → Rat) →ₗ[Rat] (Fin r → Rat) :=
  { toFun := fun x => fun j => ∑ t : Fin M, x t * (((t.1 + 1 : Nat) : Rat) ^ (n j))
    map_add' := by
      intro x y
      ext j
      simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      ext j
      simp [Finset.mul_sum, mul_assoc] }
  have hker_ne : LinearMap.ker A ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt (K := Rat)
    simpa [Module.finrank_fintype_fun_eq_card] using hrM
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hker_ne with ⟨x, hxker, hxne⟩
  let D : Nat := ∏ t : Fin M, (x t).den
  have hD_ne : D ≠ 0 := by
    dsimp [D]
    exact Finset.prod_ne_zero_iff.mpr (by intro t ht; exact Rat.den_nz (x t))
  have hden_dvd : ∀ t : Fin M, (x t).den ∣ D := by
    intro t
    dsimp [D]
    exact Finset.dvd_prod_of_mem (fun u : Fin M => (x u).den) (Finset.mem_univ t)
  let z : Fin M → Int := fun t => ((D / (x t).den : Nat) : Int) * (x t).num
  have hz_cast : ∀ t, (z t : Rat) = (D : Rat) * x t :=
    conclusion_finite_moment_audit_needs_exactly_mm_scalars_clear_den x D hden_dvd
  let hPlus : Fin M → Nat := fun t => (z t).toNat
  let hMinus : Fin M → Nat := fun t => (-(z t)).toNat
  have hzmom : ∀ j : Fin r,
      (∑ t : Fin M, (z t : Int) * (((t.1 + 1 : Nat) : Int) ^ (n j))) = 0 := by
    intro j
    have hxj :
        (∑ t : Fin M, x t * (((t.1 + 1 : Nat) : Rat) ^ (n j))) = 0 := by
      simpa [A] using congrFun (show A x = 0 from hxker) j
    have hscaled :
        (D : Rat) * (∑ t : Fin M, x t * (((t.1 + 1 : Nat) : Rat) ^ (n j))) = 0 := by
      rw [hxj, mul_zero]
    have hsumQ :
        (∑ t : Fin M, (z t : Rat) * (((t.1 + 1 : Nat) : Rat) ^ (n j))) = 0 := by
      calc
        (∑ t : Fin M, (z t : Rat) * (((t.1 + 1 : Nat) : Rat) ^ (n j))) =
            (D : Rat) * (∑ t : Fin M, x t * (((t.1 + 1 : Nat) : Rat) ^ (n j))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          rw [hz_cast t]
          ring
        _ = 0 := hscaled
    exact_mod_cast hsumQ
  have hquery : ∀ j : Fin r,
      (∑ t : Fin M, hPlus t * (t.1 + 1) ^ (n j)) =
        (∑ t : Fin M, hMinus t * (t.1 + 1) ^ (n j)) := by
    intro j
    have hsplit :
        (∑ t : Fin M, ((hPlus t : Int) - (hMinus t : Int)) *
            (((t.1 + 1 : Nat) : Int) ^ (n j))) = 0 := by
      calc
        (∑ t : Fin M, ((hPlus t : Int) - (hMinus t : Int)) *
            (((t.1 + 1 : Nat) : Int) ^ (n j))) =
            ∑ t : Fin M, (z t : Int) * (((t.1 + 1 : Nat) : Int) ^ (n j)) := by
          apply Finset.sum_congr rfl
          intro t ht
          dsimp [hPlus, hMinus]
          rw [← conclusion_finite_moment_audit_needs_exactly_mm_scalars_int_split (z t)]
        _ = 0 := hzmom j
    have hEqInt :
        (∑ t : Fin M, (hPlus t : Int) * (((t.1 + 1 : Nat) : Int) ^ (n j))) =
          (∑ t : Fin M, (hMinus t : Int) * (((t.1 + 1 : Nat) : Int) ^ (n j))) := by
      rw [← sub_eq_zero]
      simpa [Finset.sum_sub_distrib, sub_mul] using hsplit
    exact_mod_cast hEqInt
  have hhm : hPlus = hMinus := hcomplete hPlus hMinus hquery
  have hz_zero : z = 0 := by
    funext t
    have hs := congrFun hhm t
    have hsplit := conclusion_finite_moment_audit_needs_exactly_mm_scalars_int_split (z t)
    have hsInt : ((z t).toNat : Int) = ((-(z t)).toNat : Int) := by
      exact_mod_cast (by simpa [hPlus, hMinus] using hs)
    rw [hsInt, sub_self] at hsplit
    exact hsplit
  have hx_zero : x = 0 := by
    funext t
    have hzq : (z t : Rat) = 0 := by
      exact_mod_cast congrFun hz_zero t
    rw [hz_cast t] at hzq
    have hDQ : (D : Rat) ≠ 0 := by exact_mod_cast hD_ne
    exact (mul_eq_zero.mp hzq).resolve_left hDQ
  exact hxne hx_zero

end Omega.Conclusion
