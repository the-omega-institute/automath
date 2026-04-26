import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

namespace Omega.Zeta

open Set

lemma xi_strip_forbidden_real_strictMonoOn_pos :
    StrictMonoOn (fun y : ℝ => y + y⁻¹) (Set.Ici 1) := by
  intro x hx y hy hxy
  rw [← sub_pos]
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hypos : 0 < y := by linarith
  have hy_gt_one : 1 < y := hx.trans_lt hxy
  have hxyprod : 1 < x * y := by
    calc
      1 < y := hy_gt_one
      _ = 1 * y := by ring
      _ ≤ x * y := mul_le_mul_of_nonneg_right hx hypos.le
  field_simp [hxpos.ne', hypos.ne']
  nlinarith

lemma xi_strip_forbidden_real_image_pos (a : ℝ) (ha : 1 < a) :
    (fun y : ℝ => y + y⁻¹) '' Set.Ioo 1 a = Set.Ioo 2 (a + a⁻¹) := by
  ext S
  constructor
  · intro hS
    rcases hS with ⟨y, hy, rfl⟩
    have hmono_Icc :
        StrictMonoOn (fun y : ℝ => y + y⁻¹) (Set.Icc 1 a) :=
      xi_strip_forbidden_real_strictMonoOn_pos.mono Set.Icc_subset_Ici_self
    have hmem := hmono_Icc.mapsTo_Ioo hy
    norm_num at hmem ⊢
    exact hmem
  · intro hS
    have hcont : ContinuousOn (fun y : ℝ => y + y⁻¹) (Set.Icc 1 a) := by
      exact continuousOn_id.add (continuousOn_id.inv₀ (by
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))
    have himage :
        Set.Ioo ((fun y : ℝ => y + y⁻¹) 1) ((fun y : ℝ => y + y⁻¹) a) ⊆
          (fun y : ℝ => y + y⁻¹) '' Set.Ioo 1 a :=
      intermediate_value_Ioo ha.le hcont
    have hS' : S ∈ Set.Ioo ((fun y : ℝ => y + y⁻¹) 1) ((fun y : ℝ => y + y⁻¹) a) := by
      norm_num at hS ⊢
      exact hS
    exact himage hS'

lemma xi_strip_forbidden_real_abs_split (a y : ℝ) :
    (1 < |y| ∧ |y| < a) ↔ y ∈ Set.Ioo 1 a ∪ Set.Ioo (-a) (-1) := by
  constructor
  · rintro ⟨hy1, hya⟩
    by_cases hy_nonneg : 0 ≤ y
    · left
      constructor
      · simpa [abs_of_nonneg hy_nonneg] using hy1
      · simpa [abs_of_nonneg hy_nonneg] using hya
    · have hyneg : y < 0 := lt_of_not_ge hy_nonneg
      right
      constructor
      · have hneg_lt : -y < a := by simpa [abs_of_neg hyneg] using hya
        linarith
      · have hlt_neg_one : 1 < -y := by simpa [abs_of_neg hyneg] using hy1
        linarith
  · rintro (hy | hy)
    · constructor
      · have hy_nonneg : 0 ≤ y := le_of_lt (zero_lt_one.trans hy.1)
        simpa [abs_of_nonneg hy_nonneg] using hy.1
      · have hy_nonneg : 0 ≤ y := le_of_lt (zero_lt_one.trans hy.1)
        simpa [abs_of_nonneg hy_nonneg] using hy.2
    · constructor
      · have hyneg : y < 0 := hy.2.trans (by norm_num)
        have : 1 < -y := by simpa using neg_lt_neg hy.2
        simpa [abs_of_neg hyneg] using this
      · have hyneg : y < 0 := hy.2.trans (by norm_num)
        have : -y < a := by simpa using neg_lt_neg hy.1
        simpa [abs_of_neg hyneg] using this

/-- Paper label: `prop:xi-strip-forbidden-real`. -/
theorem paper_xi_strip_forbidden_real (L S : ℝ) (hL : 1 < L) :
    ((∃ y : ℝ, 1 < |y| ∧ |y| < Real.sqrt L ∧ S = y + y⁻¹) ↔
      S ∈ Set.Ioo 2 (Real.sqrt L + (Real.sqrt L)⁻¹) ∪
        Set.Ioo (-(Real.sqrt L + (Real.sqrt L)⁻¹)) (-2)) := by
  set a : ℝ := Real.sqrt L
  have ha : 1 < a := by
    change 1 < Real.sqrt L
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hL
  have hapos : 0 < a := zero_lt_one.trans ha
  have hpos_image :
      (fun y : ℝ => y + y⁻¹) '' Set.Ioo 1 a = Set.Ioo 2 (a + a⁻¹) :=
    xi_strip_forbidden_real_image_pos a ha
  constructor
  · rintro ⟨y, hy1, hya, hS⟩
    have hysplit := (xi_strip_forbidden_real_abs_split a y).mp ⟨hy1, hya⟩
    rcases hysplit with hypos | hyneg
    · left
      exact hpos_image ▸ ⟨y, hypos, hS.symm⟩
    · right
      have hmem_pos : -S ∈ (fun y : ℝ => y + y⁻¹) '' Set.Ioo 1 a := by
        refine ⟨-y, ?_, ?_⟩
        · constructor <;> linarith [hyneg.1, hyneg.2]
        · show -y + (-y)⁻¹ = -S
          rw [hS]
          field_simp
          ring
      have hinterval : -S ∈ Set.Ioo 2 (a + a⁻¹) := by
        simpa [hpos_image] using hmem_pos
      constructor <;> linarith [hinterval.1, hinterval.2]
  · rintro (hSpos | hSneg)
    · have hSpos_image : S ∈ (fun y : ℝ => y + y⁻¹) '' Set.Ioo 1 a := by
        simpa [hpos_image] using hSpos
      rcases hSpos_image with ⟨y, hy, hSy⟩
      have habs := (xi_strip_forbidden_real_abs_split a y).mpr (Or.inl hy)
      exact ⟨y, habs.1, habs.2, hSy.symm⟩
    · have hneg_interval : -S ∈ Set.Ioo 2 (a + a⁻¹) := by
        constructor <;> linarith [hSneg.1, hSneg.2]
      have hneg_pos : -S ∈ (fun y : ℝ => y + y⁻¹) '' Set.Ioo 1 a := by
        simpa [hpos_image] using hneg_interval
      rcases hneg_pos with ⟨t, ht, htS⟩
      have habs := (xi_strip_forbidden_real_abs_split a (-t)).mpr
        (Or.inr ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      refine ⟨-t, habs.1, habs.2, ?_⟩
      calc
        S = -(t + t⁻¹) := by linarith
        _ = -t + (-t)⁻¹ := by
          rw [inv_neg]
          ring

end Omega.Zeta
