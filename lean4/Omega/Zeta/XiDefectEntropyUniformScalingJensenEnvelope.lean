import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-defect-entropy-uniform-scaling-jensen-envelope`. -/
theorem paper_xi_defect_entropy_uniform_scaling_jensen_envelope {n : ℕ} (w p : Fin n → ℝ)
    (κ m S Sm : ℝ) (hκ : κ = ∑ j, w j) (hκpos : 0 < κ) (hw : ∀ j, 0 ≤ w j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hS : S = ∑ j, w j * p j)
    (hSm : Sm = ∑ j, w j * (m * p j / (1 + (m - 1) * p j))) :
    (1 < m → Sm ≤ κ * (m * (S / κ) / (1 + (m - 1) * (S / κ)))) ∧
      (0 < m → m < 1 →
        κ * (m * (S / κ) / (1 + (m - 1) * (S / κ))) ≤ Sm) := by
  classical
  let μ : ℝ := S / κ
  have hκ_ne : κ ≠ 0 := ne_of_gt hκpos
  have hS_nonneg : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hp0 j)
  have hS_le_κ : S ≤ κ := by
    rw [hS, hκ]
    exact Finset.sum_le_sum fun j _ => by
      exact mul_le_of_le_one_right (hw j) (hp1 j)
  have hμ_nonneg : 0 ≤ μ := by
    exact div_nonneg hS_nonneg hκpos.le
  have hμ_le_one : μ ≤ 1 := by
    dsimp [μ]
    exact (div_le_one hκpos).mpr hS_le_κ
  have hsum_center : (∑ j, w j * (p j - μ)) = 0 := by
    calc
      (∑ j, w j * (p j - μ)) = (∑ j, w j * p j) - ∑ j, w j * μ := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ = (∑ j, w j * p j) - (∑ j, w j) * μ := by rw [Finset.sum_mul]
      _ = S - κ * μ := by rw [← hS, ← hκ]
      _ = 0 := by
        dsimp [μ]
        field_simp [hκ_ne]
        ring_nf
  constructor
  · intro hm
    have hm_pos : 0 < m := lt_trans zero_lt_one hm
    let d : ℝ := m / (1 + (m - 1) * μ) ^ 2
    have hdenμ_pos : 0 < 1 + (m - 1) * μ := by
      have hb_nonneg : 0 ≤ m - 1 := by linarith
      nlinarith [mul_nonneg hb_nonneg hμ_nonneg]
    have htangent :
        ∀ j : Fin n,
          m * p j / (1 + (m - 1) * p j) ≤
            m * μ / (1 + (m - 1) * μ) + d * (p j - μ) := by
      intro j
      have hdenp_pos : 0 < 1 + (m - 1) * p j := by
        have hb_nonneg : 0 ≤ m - 1 := by linarith
        nlinarith [mul_nonneg hb_nonneg (hp0 j)]
      have hdenp_alt_ne : 1 - p j + p j * m ≠ 0 := by
        nlinarith [hdenp_pos]
      have hid :
          m * p j / (1 + (m - 1) * p j) -
              (m * μ / (1 + (m - 1) * μ) + d * (p j - μ)) =
            -(m * (m - 1) * (p j - μ) ^ 2) /
              ((1 + (m - 1) * p j) * (1 + (m - 1) * μ) ^ 2) := by
        dsimp [d]
        field_simp [hdenp_pos.ne', hdenp_alt_ne, hdenμ_pos.ne']
        ring_nf
        field_simp [hdenp_alt_ne]
        ring
      have hnonpos :
          -(m * (m - 1) * (p j - μ) ^ 2) /
              ((1 + (m - 1) * p j) * (1 + (m - 1) * μ) ^ 2) ≤ 0 := by
        have hnum_nonneg : 0 ≤ m * (m - 1) * (p j - μ) ^ 2 := by
          exact mul_nonneg (mul_nonneg hm_pos.le (by linarith)) (sq_nonneg _)
        have hden_nonneg :
            0 ≤ (1 + (m - 1) * p j) * (1 + (m - 1) * μ) ^ 2 := by
          exact mul_nonneg hdenp_pos.le (sq_nonneg _)
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum_nonneg) hden_nonneg
      linarith
    have hsum_le :
        (∑ j, w j * (m * p j / (1 + (m - 1) * p j))) ≤
          ∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ)) := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact mul_le_mul_of_nonneg_left (htangent j) (hw j)
    have hsum_tangent :
        (∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ))) =
          κ * (m * μ / (1 + (m - 1) * μ)) := by
      calc
        (∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ))) =
            ∑ j, (w j * (m * μ / (1 + (m - 1) * μ)) +
              d * (w j * (p j - μ))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        _ = ∑ j, w j * (m * μ / (1 + (m - 1) * μ)) +
              ∑ j, d * (w j * (p j - μ)) := by rw [Finset.sum_add_distrib]
        _ = (∑ j, w j) * (m * μ / (1 + (m - 1) * μ)) +
              d * ∑ j, w j * (p j - μ) := by
          rw [Finset.sum_mul, Finset.mul_sum]
        _ = κ * (m * μ / (1 + (m - 1) * μ)) := by rw [hκ.symm, hsum_center, mul_zero, add_zero]
    calc
      Sm = ∑ j, w j * (m * p j / (1 + (m - 1) * p j)) := hSm
      _ ≤ ∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ)) := hsum_le
      _ = κ * (m * μ / (1 + (m - 1) * μ)) := hsum_tangent
      _ = κ * (m * (S / κ) / (1 + (m - 1) * (S / κ))) := by rfl
  · intro hm_pos hm_lt
    let d : ℝ := m / (1 + (m - 1) * μ) ^ 2
    have hdenμ_pos : 0 < 1 + (m - 1) * μ := by
      have hb_nonpos : m - 1 ≤ 0 := by linarith
      have hgap_nonneg : 0 ≤ 1 - μ := by linarith
      have hprod_nonpos : (m - 1) * (1 - μ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hb_nonpos hgap_nonneg
      have hle : m ≤ 1 + (m - 1) * μ := by nlinarith
      exact lt_of_lt_of_le hm_pos hle
    have htangent :
        ∀ j : Fin n,
          m * μ / (1 + (m - 1) * μ) + d * (p j - μ) ≤
            m * p j / (1 + (m - 1) * p j) := by
      intro j
      have hdenp_pos : 0 < 1 + (m - 1) * p j := by
        have hb_nonpos : m - 1 ≤ 0 := by linarith
        have hgap_nonneg : 0 ≤ 1 - p j := by linarith [hp1 j]
        have hprod_nonpos : (m - 1) * (1 - p j) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hb_nonpos hgap_nonneg
        have hle : m ≤ 1 + (m - 1) * p j := by nlinarith
        exact lt_of_lt_of_le hm_pos hle
      have hdenp_alt_ne : 1 - p j + p j * m ≠ 0 := by
        nlinarith [hdenp_pos]
      have hid :
          m * p j / (1 + (m - 1) * p j) -
              (m * μ / (1 + (m - 1) * μ) + d * (p j - μ)) =
            -(m * (m - 1) * (p j - μ) ^ 2) /
              ((1 + (m - 1) * p j) * (1 + (m - 1) * μ) ^ 2) := by
        dsimp [d]
        field_simp [hdenp_pos.ne', hdenp_alt_ne, hdenμ_pos.ne']
        ring_nf
        field_simp [hdenp_alt_ne]
        ring
      have hnonneg :
          0 ≤ -(m * (m - 1) * (p j - μ) ^ 2) /
              ((1 + (m - 1) * p j) * (1 + (m - 1) * μ) ^ 2) := by
        have hcore_nonpos : m * (m - 1) * (p j - μ) ^ 2 ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos hm_pos.le (by linarith)) (sq_nonneg _)
        have hden_nonneg :
            0 ≤ (1 + (m - 1) * p j) * (1 + (m - 1) * μ) ^ 2 := by
          exact mul_nonneg hdenp_pos.le (sq_nonneg _)
        exact div_nonneg (neg_nonneg.mpr hcore_nonpos) hden_nonneg
      linarith
    have hsum_le :
        (∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ))) ≤
          ∑ j, w j * (m * p j / (1 + (m - 1) * p j)) := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact mul_le_mul_of_nonneg_left (htangent j) (hw j)
    have hsum_tangent :
        (∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ))) =
          κ * (m * μ / (1 + (m - 1) * μ)) := by
      calc
        (∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ))) =
            ∑ j, (w j * (m * μ / (1 + (m - 1) * μ)) +
              d * (w j * (p j - μ))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        _ = ∑ j, w j * (m * μ / (1 + (m - 1) * μ)) +
              ∑ j, d * (w j * (p j - μ)) := by rw [Finset.sum_add_distrib]
        _ = (∑ j, w j) * (m * μ / (1 + (m - 1) * μ)) +
              d * ∑ j, w j * (p j - μ) := by
          rw [Finset.sum_mul, Finset.mul_sum]
        _ = κ * (m * μ / (1 + (m - 1) * μ)) := by rw [hκ.symm, hsum_center, mul_zero, add_zero]
    calc
      κ * (m * (S / κ) / (1 + (m - 1) * (S / κ))) =
          κ * (m * μ / (1 + (m - 1) * μ)) := by rfl
      _ = ∑ j, w j * (m * μ / (1 + (m - 1) * μ) + d * (p j - μ)) := hsum_tangent.symm
      _ ≤ ∑ j, w j * (m * p j / (1 + (m - 1) * p j)) := hsum_le
      _ = Sm := hSm.symm

end Omega.Zeta
