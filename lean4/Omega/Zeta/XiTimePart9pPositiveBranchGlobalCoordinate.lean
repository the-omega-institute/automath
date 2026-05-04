import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

namespace Omega.Zeta

noncomputable section

theorem paper_xi_time_part9p_positive_branch_global_coordinate :
    (∀ ρ₁ ρ₂ : ℝ, 1 + Real.sqrt 2 < ρ₁ → ρ₁ < ρ₂ →
      ρ₁ * (ρ₁ ^ 2 - 2 * ρ₁ - 1) / (ρ₁ - 1) <
        ρ₂ * (ρ₂ ^ 2 - 2 * ρ₂ - 1) / (ρ₂ - 1)) ∧
    (∀ u : ℝ, 0 < u → ∃ ρ : ℝ, 1 + Real.sqrt 2 < ρ ∧
      u = ρ * (ρ ^ 2 - 2 * ρ - 1) / (ρ - 1)) ∧
    (∀ ρ₁ ρ₂ : ℝ, 1 + Real.sqrt 2 < ρ₁ → ρ₁ < ρ₂ →
      (ρ₁ ^ 3 - 3 * ρ₁ ^ 2 + ρ₁ + 1) /
          (2 * ρ₁ ^ 3 - 5 * ρ₁ ^ 2 + 4 * ρ₁ + 1) <
        (ρ₂ ^ 3 - 3 * ρ₂ ^ 2 + ρ₂ + 1) /
          (2 * ρ₂ ^ 3 - 5 * ρ₂ ^ 2 + 4 * ρ₂ + 1)) ∧
    (∀ a : ℝ, 0 < a → a < (1 / 2 : ℝ) → ∃ ρ : ℝ, 1 + Real.sqrt 2 < ρ ∧
      a = (ρ ^ 3 - 3 * ρ ^ 2 + ρ + 1) /
        (2 * ρ ^ 3 - 5 * ρ ^ 2 + 4 * ρ + 1)) := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_lt_two : Real.sqrt 2 < (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  constructor
  · intro ρ₁ ρ₂ hρ₁ hρ₁₂
    have h₁pos : 0 < ρ₁ - 1 := by linarith
    have h₂pos : 0 < ρ₂ - 1 := by linarith
    have h₁ne : ρ₁ - 1 ≠ 0 := ne_of_gt h₁pos
    have h₂ne : ρ₂ - 1 ≠ 0 := ne_of_gt h₂pos
    have hdiff :
        ρ₂ * (ρ₂ ^ 2 - 2 * ρ₂ - 1) / (ρ₂ - 1) -
            ρ₁ * (ρ₁ ^ 2 - 2 * ρ₁ - 1) / (ρ₁ - 1) =
          (ρ₂ - ρ₁) *
              ((ρ₁ - 1) ^ 2 * (ρ₂ - 1) + (ρ₁ - 1) * (ρ₂ - 1) ^ 2 +
                (ρ₁ - 1) * (ρ₂ - 1) + 2) /
            ((ρ₁ - 1) * (ρ₂ - 1)) := by
      field_simp [h₁ne, h₂ne]
      ring
    have hnum :
        0 <
          (ρ₁ - 1) ^ 2 * (ρ₂ - 1) + (ρ₁ - 1) * (ρ₂ - 1) ^ 2 +
            (ρ₁ - 1) * (ρ₂ - 1) + 2 := by
      have hA : 0 < (ρ₁ - 1) ^ 2 * (ρ₂ - 1) := by positivity
      have hB : 0 < (ρ₁ - 1) * (ρ₂ - 1) ^ 2 := by positivity
      have hC : 0 < (ρ₁ - 1) * (ρ₂ - 1) := by positivity
      nlinarith
    have hpos :
        0 <
          (ρ₂ - ρ₁) *
              ((ρ₁ - 1) ^ 2 * (ρ₂ - 1) + (ρ₁ - 1) * (ρ₂ - 1) ^ 2 +
                (ρ₁ - 1) * (ρ₂ - 1) + 2) /
            ((ρ₁ - 1) * (ρ₂ - 1)) := by
      exact div_pos (mul_pos (sub_pos.2 hρ₁₂) hnum) (mul_pos h₁pos h₂pos)
    linarith
  constructor
  · intro u hu
    let g : ℝ → ℝ := fun t => t ^ 2 + t - 2 - 2 / t
    let b : ℝ := u + 3
    have hbpos : 0 < b := by dsimp [b]; linarith
    have hbsqrt : Real.sqrt 2 < b := by dsimp [b]; linarith
    have hbgt2 : 2 < b := by dsimp [b]; linarith
    have hg_cont : ContinuousOn g (Set.Icc (Real.sqrt 2) b) := by
      dsimp [g]
      refine ContinuousOn.sub ?_ ?_
      · fun_prop
      · refine ContinuousOn.div ?_ ?_ ?_
        · fun_prop
        · fun_prop
        · intro x hx
          exact ne_of_gt (lt_of_lt_of_le hsqrt2_pos hx.1)
    have hg0 : g (Real.sqrt 2) = 0 := by
      dsimp [g]
      have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
      field_simp [hne]
      ring_nf
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hgb : u < g b := by
      have hfrac : -1 < -(2 / b) := by
        have hlt : 2 / b < 1 := by
          field_simp [ne_of_gt hbpos]
          linarith
        linarith
      dsimp [g, b] at hfrac ⊢
      nlinarith [sq_nonneg u]
    have humem : u ∈ Set.Ioo (g (Real.sqrt 2)) (g b) := by
      simpa [hg0] using And.intro hu hgb
    rcases intermediate_value_Ioo (le_of_lt hbsqrt) hg_cont humem with ⟨t, ht, hgt⟩
    refine ⟨t + 1, by linarith [ht.1], ?_⟩
    have htpos : 0 < t := lt_trans hsqrt2_pos ht.1
    have htne : t ≠ 0 := ne_of_gt htpos
    have hrewrite :
        (t + 1) * ((t + 1) ^ 2 - 2 * (t + 1) - 1) / (t + 1 - 1) = g t := by
      dsimp [g]
      field_simp [htne]
      ring
    rw [← hgt, ← hrewrite]
  constructor
  · intro ρ₁ ρ₂ hρ₁ hρ₁₂
    let t₁ : ℝ := ρ₁ - 1
    let t₂ : ℝ := ρ₂ - 1
    have ht₁sqrt : Real.sqrt 2 < t₁ := by dsimp [t₁]; linarith
    have ht₂sqrt : Real.sqrt 2 < t₂ := by dsimp [t₂]; linarith
    have ht₁pos : 0 < t₁ := lt_trans hsqrt2_pos ht₁sqrt
    have ht₂pos : 0 < t₂ := lt_trans hsqrt2_pos ht₂sqrt
    have ht₁₂ : t₁ < t₂ := by dsimp [t₁, t₂]; linarith
    have ht₁sq' : (Real.sqrt 2) ^ 2 < t₁ ^ 2 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg 2) (le_of_lt ht₁pos)).2 ht₁sqrt
    have ht₂sq' : (Real.sqrt 2) ^ 2 < t₂ ^ 2 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg 2) (le_of_lt ht₂pos)).2 ht₂sqrt
    have ht₁sq : 2 < t₁ ^ 2 := by
      simpa [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using ht₁sq'
    have ht₂sq : 2 < t₂ ^ 2 := by
      simpa [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using ht₂sq'
    have hden₁pos : 0 < 2 * t₁ ^ 3 + t₁ ^ 2 + 2 := by positivity
    have hden₂pos : 0 < 2 * t₂ ^ 3 + t₂ ^ 2 + 2 := by positivity
    have hnum :
        0 <
          t₁ ^ 2 * t₂ ^ 2 + 4 * t₁ ^ 2 * t₂ + 2 * t₁ ^ 2 +
            4 * t₁ * t₂ ^ 2 + 4 * t₁ * t₂ + 2 * t₂ ^ 2 - 4 := by
      have hprod : 4 < t₁ ^ 2 * t₂ ^ 2 := by nlinarith
      have hA : 0 < 4 * t₁ ^ 2 * t₂ := by positivity
      have hB : 0 < 2 * t₁ ^ 2 := by positivity
      have hC : 0 < 4 * t₁ * t₂ ^ 2 := by positivity
      have hD : 0 < 4 * t₁ * t₂ := by positivity
      have hE : 0 < 2 * t₂ ^ 2 := by positivity
      nlinarith
    have hρ₁den :
        2 * ρ₁ ^ 3 - 5 * ρ₁ ^ 2 + 4 * ρ₁ + 1 = 2 * t₁ ^ 3 + t₁ ^ 2 + 2 := by
      dsimp [t₁]
      ring
    have hρ₂den :
        2 * ρ₂ ^ 3 - 5 * ρ₂ ^ 2 + 4 * ρ₂ + 1 = 2 * t₂ ^ 3 + t₂ ^ 2 + 2 := by
      dsimp [t₂]
      ring
    have hρ₁num : ρ₁ ^ 3 - 3 * ρ₁ ^ 2 + ρ₁ + 1 = t₁ * (t₁ ^ 2 - 2) := by
      dsimp [t₁]
      ring
    have hρ₂num : ρ₂ ^ 3 - 3 * ρ₂ ^ 2 + ρ₂ + 1 = t₂ * (t₂ ^ 2 - 2) := by
      dsimp [t₂]
      ring
    have hdiff :
        t₂ * (t₂ ^ 2 - 2) / (2 * t₂ ^ 3 + t₂ ^ 2 + 2) -
            t₁ * (t₁ ^ 2 - 2) / (2 * t₁ ^ 3 + t₁ ^ 2 + 2) =
          (t₂ - t₁) *
              (t₁ ^ 2 * t₂ ^ 2 + 4 * t₁ ^ 2 * t₂ + 2 * t₁ ^ 2 +
                4 * t₁ * t₂ ^ 2 + 4 * t₁ * t₂ + 2 * t₂ ^ 2 - 4) /
            ((2 * t₁ ^ 3 + t₁ ^ 2 + 2) * (2 * t₂ ^ 3 + t₂ ^ 2 + 2)) := by
      field_simp [ne_of_gt hden₁pos, ne_of_gt hden₂pos]
      ring_nf
    have hpos :
        0 <
          (t₂ - t₁) *
              (t₁ ^ 2 * t₂ ^ 2 + 4 * t₁ ^ 2 * t₂ + 2 * t₁ ^ 2 +
                4 * t₁ * t₂ ^ 2 + 4 * t₁ * t₂ + 2 * t₂ ^ 2 - 4) /
            ((2 * t₁ ^ 3 + t₁ ^ 2 + 2) * (2 * t₂ ^ 3 + t₂ ^ 2 + 2)) := by
      exact div_pos (mul_pos (sub_pos.2 ht₁₂) hnum) (mul_pos hden₁pos hden₂pos)
    rw [hρ₁num, hρ₂num, hρ₁den, hρ₂den]
    linarith
  · intro a ha0 ha_half
    let α : ℝ → ℝ := fun t => t * (t ^ 2 - 2) / (2 * t ^ 3 + t ^ 2 + 2)
    let δ : ℝ := (1 / 2 : ℝ) - a
    let b : ℝ := 10 / δ + 2
    have hδpos : 0 < δ := by dsimp [δ]; linarith
    have hbpos : 0 < b := by dsimp [b]; positivity
    have hbge2 : 2 ≤ b := by
      have hnonneg : 0 ≤ 10 / δ := by positivity
      dsimp [b]
      linarith
    have hbsqrt : Real.sqrt 2 < b := lt_of_lt_of_le hsqrt2_lt_two hbge2
    have hα_cont : ContinuousOn α (Set.Icc (Real.sqrt 2) b) := by
      dsimp [α]
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro x hx
        have hxpos : 0 < x := lt_of_lt_of_le hsqrt2_pos hx.1
        have hdenpos : 0 < 2 * x ^ 3 + x ^ 2 + 2 := by positivity
        exact ne_of_gt hdenpos
    have hα0 : α (Real.sqrt 2) = 0 := by
      dsimp [α]
      have hdenne : 2 * (Real.sqrt 2) ^ 3 + (Real.sqrt 2) ^ 2 + 2 ≠ 0 := by
        positivity
      field_simp [hdenne]
      ring_nf
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hdenbpos : 0 < 2 * b ^ 3 + b ^ 2 + 2 := by positivity
    have hgap_id :
        (1 / 2 : ℝ) - α b =
          (b ^ 2 + 4 * b + 2) / (2 * (2 * b ^ 3 + b ^ 2 + 2)) := by
      dsimp [α]
      field_simp [ne_of_gt hdenbpos]
      ring
    have hgap_le : (b ^ 2 + 4 * b + 2) / (2 * (2 * b ^ 3 + b ^ 2 + 2)) ≤ 1 / b := by
      have hnum_le : b ^ 2 + 4 * b + 2 ≤ 4 * b ^ 2 := by nlinarith
      have hdenpos' : 0 < 2 * (2 * b ^ 3 + b ^ 2 + 2) := by positivity
      field_simp [ne_of_gt hbpos, ne_of_gt hdenpos']
      nlinarith [hnum_le]
    have hone_over_lt : 1 / b < δ := by
      field_simp [ne_of_gt hbpos, ne_of_gt hδpos]
      dsimp [b]
      field_simp [ne_of_gt hδpos]
      nlinarith
    have hαb : a < α b := by
      have hgap_lt : (1 / 2 : ℝ) - α b < δ := by
        rw [hgap_id]
        exact lt_of_le_of_lt hgap_le hone_over_lt
      dsimp [δ] at hgap_lt
      linarith
    have hamem : a ∈ Set.Ioo (α (Real.sqrt 2)) (α b) := by
      simpa [hα0] using And.intro ha0 hαb
    rcases intermediate_value_Ioo (le_of_lt hbsqrt) hα_cont hamem with ⟨t, ht, hαt⟩
    refine ⟨t + 1, by linarith [ht.1], ?_⟩
    have htpos : 0 < t := lt_trans hsqrt2_pos ht.1
    have htdenpos : 0 < 2 * t ^ 3 + t ^ 2 + 2 := by positivity
    have hrewrite :
        ((t + 1) ^ 3 - 3 * (t + 1) ^ 2 + (t + 1) + 1) /
            (2 * (t + 1) ^ 3 - 5 * (t + 1) ^ 2 + 4 * (t + 1) + 1) = α t := by
      have hden :
          2 * (t + 1) ^ 3 - 5 * (t + 1) ^ 2 + 4 * (t + 1) + 1 =
            2 * t ^ 3 + t ^ 2 + 2 := by
        ring
      rw [hden]
      dsimp [α]
      field_simp [ne_of_gt htdenpos]
      ring_nf
    rw [← hαt, ← hrewrite]

end

end Omega.Zeta
