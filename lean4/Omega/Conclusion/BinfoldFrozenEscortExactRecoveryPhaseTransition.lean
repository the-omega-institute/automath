import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The reduced frozen-escort success law after concentration on the maximal fiber:
`min(M_m, 2^{B_m}) / M_m` with `M_m = 2^{α m}` and `B_m = β m`. -/
noncomputable def binfoldFrozenEscortReducedSuccess (α β m : ℕ) : ℝ :=
  min ((2 : ℝ) ^ (α * m)) ((2 : ℝ) ^ (β * m)) / (2 : ℝ) ^ (α * m)

private lemma binfoldFrozenEscortReducedSuccess_eq_one_of_le (hαβ : α ≤ β) :
    ∀ m, binfoldFrozenEscortReducedSuccess α β m = 1 := by
  intro m
  unfold binfoldFrozenEscortReducedSuccess
  have hpow : (2 : ℝ) ^ (α * m) ≤ (2 : ℝ) ^ (β * m) := by
    apply pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
    exact Nat.mul_le_mul_right m hαβ
  rw [min_eq_left hpow, div_self]
  positivity

private lemma binfoldFrozenEscortReducedSuccess_eq_geom_of_lt (hβα : β < α) :
    ∃ k : ℕ, α = β + (k + 1) ∧
      ∀ m, binfoldFrozenEscortReducedSuccess α β m = (((1 / 2 : ℝ) ^ (k + 1)) ^ m) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hβα
  refine ⟨k, hk, ?_⟩
  intro m
  unfold binfoldFrozenEscortReducedSuccess
  have hexp : α * m = β * m + (k + 1) * m := by
    rw [hk]
    ring
  have hpow : (2 : ℝ) ^ (β * m) ≤ (2 : ℝ) ^ (α * m) := by
    apply pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
    calc
      β * m ≤ β * m + (k + 1) * m := Nat.le_add_right _ _
      _ = α * m := hexp.symm
  rw [min_eq_right hpow, hexp, pow_add]
  have hβnz : (2 : ℝ) ^ (β * m) ≠ 0 := by positivity
  have hdiv :
      (2 : ℝ) ^ (β * m) / ((2 : ℝ) ^ (β * m) * (2 : ℝ) ^ ((k + 1) * m)) =
        1 / (2 : ℝ) ^ ((k + 1) * m) := by
    field_simp [hβnz]
  rw [hdiv]
  simp [pow_mul, one_div]

/-- Paper label: `thm:conclusion-binfold-frozen-escort-exact-recovery-phase-transition`.
After frozen-mass concentration reduces the escort success law to `min(M_m, 2^{B_m}) / M_m`
with `M_m = 2^{α m}` and `B_m = β m`, the maximal-fiber exponent `α` gives the sharp
binary threshold `β = α`.
-/
theorem paper_conclusion_binfold_frozen_escort_exact_recovery_phase_transition (α β : ℕ) :
    ((β < α) →
      Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop
        (nhds 0)) ∧
    ((α < β) →
      Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop
        (nhds 1)) := by
  refine ⟨?_, ?_⟩
  · intro hβα
    obtain ⟨k, _, hgeom⟩ := binfoldFrozenEscortReducedSuccess_eq_geom_of_lt hβα
    have hbase : |(1 / 2 : ℝ) ^ (k + 1)| < 1 := by
      have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
      rw [abs_of_nonneg hnonneg]
      exact pow_lt_one₀ (by positivity) (by norm_num) (Nat.succ_ne_zero _)
    convert tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase using 1
    ext m
    exact hgeom m
  · intro hαβ
    have hconst : ∀ m, binfoldFrozenEscortReducedSuccess α β m = 1 :=
      binfoldFrozenEscortReducedSuccess_eq_one_of_le hαβ.le
    convert tendsto_const_nhds using 1
    ext m
    exact hconst m

end Omega.Conclusion
