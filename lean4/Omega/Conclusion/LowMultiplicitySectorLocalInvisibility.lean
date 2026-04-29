import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Omega.Conclusion

lemma conclusion_low_multiplicity_sector_local_invisibility_left_sum
    {X : Type*} [Fintype X] (d : X → ℕ) (k : ℕ) (ε : ℝ)
    (hk1 : 1 ≤ k) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ x : X, min ((d x : ℝ)) (k : ℝ)) -
        (∑ x : X, min ((d x : ℝ)) ((k : ℝ) - ε)) =
      ε * (Finset.univ.filter (fun x : X => k ≤ d x)).card := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ x : X, (min ((d x : ℝ)) (k : ℝ) - min ((d x : ℝ)) ((k : ℝ) - ε))) =
        Finset.sum (Finset.univ.filter (fun x : X => k ≤ d x)) (fun _ => ε) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases hxk : k ≤ d x
      · have hk_le_dx : (k : ℝ) ≤ d x := by exact_mod_cast hxk
        have hkε_le_dx : (k : ℝ) - ε ≤ d x := le_trans (sub_le_self _ hε0.le) hk_le_dx
        rw [min_eq_right hk_le_dx, min_eq_right hkε_le_dx]
        simp [hxk]
      · have hdx_lt_k : d x < k := Nat.lt_of_not_ge hxk
        have hdx_le_pred : d x ≤ k - 1 := Nat.le_pred_of_lt hdx_lt_k
        have hpred_le : (k - 1 : ℕ) ≤ (k : ℝ) - ε := by
          have hk_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub hk1]
            norm_num
          rw [hk_cast]
          linarith
        have hdx_le_kε : (d x : ℝ) ≤ (k : ℝ) - ε := by
          exact le_trans (by exact_mod_cast hdx_le_pred) hpred_le
        have hdx_le_k : (d x : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt hdx_lt_k
        simp [hxk, min_eq_left hdx_le_k, min_eq_left hdx_le_kε]
    _ = ε * (Finset.univ.filter (fun x : X => k ≤ d x)).card := by
      simp [mul_comm]

lemma conclusion_low_multiplicity_sector_local_invisibility_right_sum
    {X : Type*} [Fintype X] (d : X → ℕ) (k : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ x : X, min ((d x : ℝ)) ((k : ℝ) + ε)) -
        (∑ x : X, min ((d x : ℝ)) (k : ℝ)) =
      ε * (Finset.univ.filter (fun x : X => k + 1 ≤ d x)).card := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ x : X, (min ((d x : ℝ)) ((k : ℝ) + ε) - min ((d x : ℝ)) (k : ℝ))) =
        Finset.sum (Finset.univ.filter (fun x : X => k + 1 ≤ d x)) (fun _ => ε) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases hxk : k + 1 ≤ d x
      · have hk_le_dx : (k : ℝ) ≤ d x := by exact_mod_cast (Nat.le_trans (Nat.le_succ k) hxk)
        have hkε_le_succ : (k : ℝ) + ε ≤ (k + 1 : ℕ) := by
          norm_num [Nat.cast_add]
          linarith
        have hkε_le_dx : (k : ℝ) + ε ≤ d x := by
          exact le_trans hkε_le_succ (by exact_mod_cast hxk)
        simp [hxk, min_eq_right hkε_le_dx, min_eq_right hk_le_dx]
      · have hdx_le_k : d x ≤ k := by omega
        have hdx_le_k_real : (d x : ℝ) ≤ k := by exact_mod_cast hdx_le_k
        have hdx_le_kε : (d x : ℝ) ≤ (k : ℝ) + ε := le_trans hdx_le_k_real (by linarith)
        simp [hxk, min_eq_left hdx_le_kε, min_eq_left hdx_le_k_real]
    _ = ε * (Finset.univ.filter (fun x : X => k + 1 ≤ d x)).card := by
      simp [mul_comm]

lemma conclusion_low_multiplicity_sector_local_invisibility_card_eq_tail_sub_tail_succ
    {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun x : X => d x = k)).card =
      (Finset.univ.filter (fun x : X => k ≤ d x)).card -
        (Finset.univ.filter (fun x : X => k + 1 ≤ d x)).card := by
  classical
  let A : Finset X := Finset.univ.filter fun x => k ≤ d x
  let B : Finset X := Finset.univ.filter fun x => k + 1 ≤ d x
  have hBA : B ⊆ A := by
    intro x hx
    simp [A, B] at hx ⊢
    omega
  have hsplit : A \ B = Finset.univ.filter (fun x => d x = k) := by
    ext x
    simp [A, B]
    omega
  have hcard :
      (Finset.univ.filter (fun x => d x = k)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

/-- Paper label: `cor:conclusion-low-multiplicity-sector-local-invisibility`. Equality of the
continuous min-capacity curves on a neighborhood of an integer `k` forces equality of the local
slope jump, hence the multiplicity at level `k`. -/
theorem paper_conclusion_low_multiplicity_sector_local_invisibility {X Y : Type*} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] (df : X → ℕ) (dh : Y → ℕ) (U : ℝ)
    (hU : 0 < U)
    (hCap : ∀ T : ℝ, 0 ≤ T → T ≤ U →
      (∑ y : Y, min ((dh y : ℝ)) T) = (∑ x : X, min ((df x : ℝ)) T))
    (k : ℕ) (hk1 : 1 ≤ k) (hkU : (k : ℝ) < U) :
    (Finset.univ.filter (fun y : Y => dh y = k)).card =
      (Finset.univ.filter (fun x : X => df x = k)).card := by
  classical
  have _hU_pos : 0 < U := hU
  let ε : ℝ := min (1 : ℝ) (U - (k : ℝ)) / 2
  have hUk_pos : 0 < U - (k : ℝ) := sub_pos.mpr hkU
  have hmin_pos : 0 < min (1 : ℝ) (U - (k : ℝ)) := lt_min (by norm_num) hUk_pos
  have hε0 : 0 < ε := by
    dsimp [ε]
    linarith
  have hε1 : ε ≤ 1 := by
    have hmin_le_one : min (1 : ℝ) (U - (k : ℝ)) ≤ 1 := min_le_left _ _
    dsimp [ε]
    linarith
  have hε_le_gap : ε ≤ U - (k : ℝ) := by
    have hmin_le_gap : min (1 : ℝ) (U - (k : ℝ)) ≤ U - (k : ℝ) := min_le_right _ _
    dsimp [ε]
    linarith
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hk_minus_nonneg : 0 ≤ (k : ℝ) - ε := by
    have hhalf : ε ≤ 1 / 2 := by
      have hmin_le_one : min (1 : ℝ) (U - (k : ℝ)) ≤ 1 := min_le_left _ _
      dsimp [ε]
      linarith
    have hk_ge_one : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  have hk_plus_le_U : (k : ℝ) + ε ≤ U := by linarith
  have hk_minus_le_U : (k : ℝ) - ε ≤ U := by linarith [hε0.le, hkU.le]
  have hcap_k := hCap (k : ℝ) hk_nonneg hkU.le
  have hcap_minus := hCap ((k : ℝ) - ε) hk_minus_nonneg hk_minus_le_U
  have hcap_plus := hCap ((k : ℝ) + ε) (by linarith [hk_nonneg, hε0.le]) hk_plus_le_U
  have hleft :
      (Finset.univ.filter (fun y : Y => k ≤ dh y)).card =
        (Finset.univ.filter (fun x : X => k ≤ df x)).card := by
    have hY :=
      conclusion_low_multiplicity_sector_local_invisibility_left_sum dh k ε hk1 hε0 hε1
    have hX :=
      conclusion_low_multiplicity_sector_local_invisibility_left_sum df k ε hk1 hε0 hε1
    have hreal :
        ε * (Finset.univ.filter (fun y : Y => k ≤ dh y)).card =
          ε * (Finset.univ.filter (fun x : X => k ≤ df x)).card := by
      linarith
    exact Nat.cast_injective (mul_left_cancel₀ hε0.ne' hreal)
  have hright :
      (Finset.univ.filter (fun y : Y => k + 1 ≤ dh y)).card =
        (Finset.univ.filter (fun x : X => k + 1 ≤ df x)).card := by
    have hY :=
      conclusion_low_multiplicity_sector_local_invisibility_right_sum dh k ε hε0 hε1
    have hX :=
      conclusion_low_multiplicity_sector_local_invisibility_right_sum df k ε hε0 hε1
    have hreal :
        ε * (Finset.univ.filter (fun y : Y => k + 1 ≤ dh y)).card =
          ε * (Finset.univ.filter (fun x : X => k + 1 ≤ df x)).card := by
      linarith
    exact Nat.cast_injective (mul_left_cancel₀ hε0.ne' hreal)
  rw [conclusion_low_multiplicity_sector_local_invisibility_card_eq_tail_sub_tail_succ dh k,
    conclusion_low_multiplicity_sector_local_invisibility_card_eq_tail_sub_tail_succ df k,
    hleft, hright]

end Omega.Conclusion
