import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-boundary-plancherel-information-identity`. -/
theorem paper_conclusion_window6_boundary_plancherel_information_identity
    {G : Type} [Fintype G] [DecidableEq G] (χ : G → G → ℝ) (one : G) (μ : G → ℝ)
    (hcard : Fintype.card G = 8) (hone : ∀ x, χ one x = 1)
    (hortho : ∀ x y, (∑ a : G, χ a x * χ a y) = if x = y then 8 else 0)
    (hμ : (∑ x : G, μ x) = 1) :
    let μhat := fun a : G => ∑ x : G, μ x * χ a x
    (∑ x : G, μ x ^ 2) = (1 / 8 : ℝ) * (∑ a : G, μhat a ^ 2) ∧
      (∑ x : G, (μ x - (1 / 8 : ℝ)) ^ 2) =
        (1 / 8 : ℝ) * (∑ a : G, if a = one then 0 else μhat a ^ 2) := by
  classical
  dsimp
  let μhat := fun a : G => ∑ x : G, μ x * χ a x
  change (∑ x : G, μ x ^ 2) = (1 / 8 : ℝ) * (∑ a : G, μhat a ^ 2) ∧
    (∑ x : G, (μ x - (1 / 8 : ℝ)) ^ 2) =
      (1 / 8 : ℝ) * (∑ a : G, if a = one then 0 else μhat a ^ 2)
  have h_expand : (∑ a : G, μhat a ^ 2) = 8 * ∑ x : G, μ x ^ 2 := by
    calc
      (∑ a : G, μhat a ^ 2)
          = ∑ a : G, ∑ x : G, ∑ y : G, (μ x * χ a x) * (μ y * χ a y) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              simp [μhat, pow_two, Finset.mul_sum, mul_left_comm, mul_comm]
      _ = ∑ x : G, ∑ y : G, ∑ a : G, (μ x * χ a x) * (μ y * χ a y) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [Finset.sum_comm]
      _ = ∑ x : G, ∑ y : G, μ x * μ y * ∑ a : G, χ a x * χ a y := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              refine Finset.sum_congr rfl ?_
              intro y hy
              simp [Finset.mul_sum, mul_left_comm, mul_comm]
      _ = ∑ x : G, ∑ y : G, μ x * μ y * (if x = y then 8 else 0) := by
              simp [hortho]
      _ = ∑ x : G, μ x * μ x * 8 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp
      _ = 8 * ∑ x : G, μ x ^ 2 := by
              simp [pow_two, Finset.mul_sum, mul_assoc, mul_comm]
  have h_parseval :
      (∑ x : G, μ x ^ 2) = (1 / 8 : ℝ) * (∑ a : G, μhat a ^ 2) := by
    nlinarith
  have h_hat_one : μhat one = 1 := by
    simp [μhat, hone, hμ]
  have h_center :
      (∑ x : G, (μ x - (1 / 8 : ℝ)) ^ 2) = (∑ x : G, μ x ^ 2) - 1 / 8 := by
    have hconst : (∑ x : G, (1 / 64 : ℝ)) = 1 / 8 := by
      simp [Finset.sum_const, hcard]
      norm_num
    calc
      (∑ x : G, (μ x - (1 / 8 : ℝ)) ^ 2)
          = ∑ x : G, (μ x ^ 2 - (1 / 4 : ℝ) * μ x + 1 / 64) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = (∑ x : G, μ x ^ 2) - (1 / 4 : ℝ) * (∑ x : G, μ x) +
            ∑ x : G, (1 / 64 : ℝ) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ x : G, μ x ^ 2) - 1 / 8 := by
              nlinarith
  have h_without_one :
      (∑ a : G, if a = one then 0 else μhat a ^ 2) =
        (∑ a : G, μhat a ^ 2) - μhat one ^ 2 := by
    have hsplit :
        (∑ a : G, μhat a ^ 2) =
          (∑ a : G, if a = one then μhat a ^ 2 else 0) +
            ∑ a : G, if a = one then 0 else μhat a ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases h : a = one <;> simp [h]
    have hone_part : (∑ a : G, if a = one then μhat a ^ 2 else 0) = μhat one ^ 2 := by
      simp
    nlinarith
  refine ⟨h_parseval, ?_⟩
  calc
    (∑ x : G, (μ x - (1 / 8 : ℝ)) ^ 2)
        = (∑ x : G, μ x ^ 2) - 1 / 8 := h_center
    _ = (1 / 8 : ℝ) * (∑ a : G, μhat a ^ 2) - 1 / 8 := by rw [h_parseval]
    _ = (1 / 8 : ℝ) * (∑ a : G, if a = one then 0 else μhat a ^ 2) := by
          rw [h_without_one, h_hat_one]
          ring

end Omega.Conclusion
