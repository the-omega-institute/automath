import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-defect-entropy-riccati-sandwich`. -/
theorem paper_xi_defect_entropy_riccati_sandwich {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (δ : ι → ℝ) (t δmin δmax κ S Sderiv : ℝ)
    (hδ : ∀ i, 0 < δ i) (hm : ∀ i, 0 < m i) (ht : 0 ≤ t)
    (hκ : κ = ∑ i, (m i : ℝ)) (hmin : ∀ i, δmin ≤ δ i)
    (hmax : ∀ i, δ i ≤ δmax) (hδmin : 0 < δmin) (hδmax : 0 < δmax)
    (hS : S = ∑ i, (m i : ℝ) * δ i / (t + 1 + δ i))
    (hSderiv : Sderiv = -∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2) :
    -(1 / (κ * δmin)) * S ^ 2 ≤ Sderiv ∧
      Sderiv ≤ -(1 / (κ * δmax)) * S ^ 2 := by
  classical
  by_cases hnonempty : Nonempty ι
  · have hκ_pos : 0 < κ := by
      rw [hκ]
      obtain ⟨j⟩ := hnonempty
      have hterm_nonneg : ∀ i, 0 ≤ (m i : ℝ) := by
        intro i
        positivity
      have hterm_pos : 0 < (m j : ℝ) := by
        exact_mod_cast hm j
      exact lt_of_lt_of_le hterm_pos
        (Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_univ j))
    have hden_pos : ∀ i, 0 < t + 1 + δ i := by
      intro i
      linarith [ht, hδ i]
    have hden_min_pos : 0 < t + 1 + δmin := by
      linarith [ht, hδmin]
    have hden_max_pos : 0 < t + 1 + δmax := by
      linarith [ht, hδmax]
    have hS_nonneg : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun i _ => by
        exact div_nonneg (mul_nonneg (by positivity) (le_of_lt (hδ i))) (le_of_lt (hden_pos i))
    have hratio_min_le : ∀ i, δmin / (t + 1 + δmin) ≤ δ i / (t + 1 + δ i) := by
      intro i
      have hmul :
          δmin * (t + 1 + δ i) ≤ δ i * (t + 1 + δmin) := by
        nlinarith [hmin i, hδmin, hδ i, ht]
      exact (div_le_div_iff₀ hden_min_pos (hden_pos i)).2 hmul
    have hratio_le_max : ∀ i, δ i / (t + 1 + δ i) ≤ δmax / (t + 1 + δmax) := by
      intro i
      have hmul :
          δ i * (t + 1 + δmax) ≤ δmax * (t + 1 + δ i) := by
        nlinarith [hmax i, hδ i, hδmax, ht]
      exact (div_le_div_iff₀ (hden_pos i) hden_max_pos).2 hmul
    have hS_ge_min :
        κ * (δmin / (t + 1 + δmin)) ≤ S := by
      rw [hκ, hS]
      calc
        (∑ i, (m i : ℝ)) * (δmin / (t + 1 + δmin)) =
            ∑ i, (m i : ℝ) * (δmin / (t + 1 + δmin)) := by
          rw [Finset.sum_mul]
        _ ≤ ∑ i, (m i : ℝ) * (δ i / (t + 1 + δ i)) := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hratio_min_le i) (by positivity)
        _ = ∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) := by
          congr
          ext i
          ring
    have hS_le_max :
        S ≤ κ * (δmax / (t + 1 + δmax)) := by
      rw [hκ, hS]
      calc
        ∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) =
            ∑ i, (m i : ℝ) * (δ i / (t + 1 + δ i)) := by
          congr
          ext i
          ring
        _ ≤ ∑ i, (m i : ℝ) * (δmax / (t + 1 + δmax)) := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hratio_le_max i) (by positivity)
        _ = (∑ i, (m i : ℝ)) * (δmax / (t + 1 + δmax)) := by
          rw [Finset.sum_mul]
    have hD_le_S_over_min :
        (∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2) ≤ S / (t + 1 + δmin) := by
      rw [hS]
      calc
        ∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2 =
            ∑ i, ((m i : ℝ) * δ i / (t + 1 + δ i)) / (t + 1 + δ i) := by
          congr
          ext i
          field_simp [(ne_of_gt (hden_pos i))]
        _ ≤ ∑ i, ((m i : ℝ) * δ i / (t + 1 + δ i)) / (t + 1 + δmin) := by
          exact Finset.sum_le_sum fun i _ => by
            have hnum_nonneg : 0 ≤ (m i : ℝ) * δ i / (t + 1 + δ i) := by
              exact div_nonneg (mul_nonneg (by positivity) (le_of_lt (hδ i)))
                (le_of_lt (hden_pos i))
            have hden_le : t + 1 + δmin ≤ t + 1 + δ i := by
              linarith [hmin i]
            exact div_le_div_of_nonneg_left hnum_nonneg hden_min_pos hden_le
        _ = (∑ i, (m i : ℝ) * δ i / (t + 1 + δ i)) / (t + 1 + δmin) := by
          rw [Finset.sum_div]
    have hD_ge_S_over_max :
        S / (t + 1 + δmax) ≤
          (∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2) := by
      rw [hS]
      calc
        (∑ i, (m i : ℝ) * δ i / (t + 1 + δ i)) / (t + 1 + δmax) =
            ∑ i, ((m i : ℝ) * δ i / (t + 1 + δ i)) / (t + 1 + δmax) := by
          rw [Finset.sum_div]
        _ ≤ ∑ i, ((m i : ℝ) * δ i / (t + 1 + δ i)) / (t + 1 + δ i) := by
          exact Finset.sum_le_sum fun i _ => by
            have hnum_nonneg : 0 ≤ (m i : ℝ) * δ i / (t + 1 + δ i) := by
              exact div_nonneg (mul_nonneg (by positivity) (le_of_lt (hδ i)))
                (le_of_lt (hden_pos i))
            have hden_le : t + 1 + δ i ≤ t + 1 + δmax := by
              linarith [hmax i]
            exact div_le_div_of_nonneg_left hnum_nonneg (hden_pos i) hden_le
        _ = ∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2 := by
          congr
          ext i
          field_simp [(ne_of_gt (hden_pos i))]
    have hD_upper :
        (∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2) ≤ S ^ 2 / (κ * δmin) := by
      have hscale : S / (t + 1 + δmin) ≤ S ^ 2 / (κ * δmin) := by
        have hmul : κ * δmin ≤ S * (t + 1 + δmin) := by
          have h := mul_le_mul_of_nonneg_right hS_ge_min (le_of_lt hden_min_pos)
          have hden_ne : t + 1 + δmin ≠ 0 := ne_of_gt hden_min_pos
          field_simp [hden_ne] at h
          nlinarith
        rw [div_le_div_iff₀ hden_min_pos (mul_pos hκ_pos hδmin)]
        nlinarith [hmul, hS_nonneg]
      exact le_trans hD_le_S_over_min hscale
    have hD_lower :
        S ^ 2 / (κ * δmax) ≤
          (∑ i, (m i : ℝ) * δ i / (t + 1 + δ i) ^ 2) := by
      have hscale : S ^ 2 / (κ * δmax) ≤ S / (t + 1 + δmax) := by
        have hmul : S * (t + 1 + δmax) ≤ κ * δmax := by
          have h := mul_le_mul_of_nonneg_right hS_le_max (le_of_lt hden_max_pos)
          have hden_ne : t + 1 + δmax ≠ 0 := ne_of_gt hden_max_pos
          field_simp [hden_ne] at h
          nlinarith
        rw [div_le_div_iff₀ (mul_pos hκ_pos hδmax) hden_max_pos]
        nlinarith [hmul, hS_nonneg]
      exact le_trans hscale hD_ge_S_over_max
    rw [hSderiv]
    constructor
    · have hneg := neg_le_neg hD_upper
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hneg
    · have hneg := neg_le_neg hD_lower
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hneg
  · have hempty : IsEmpty ι := not_nonempty_iff.mp hnonempty
    letI := hempty
    simp [hκ, hS, hSderiv]

end Omega.Zeta
