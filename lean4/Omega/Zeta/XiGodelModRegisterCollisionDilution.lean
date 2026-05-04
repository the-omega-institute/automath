import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

lemma xi_godel_mod_register_collision_dilution_probability_l2_lipschitz
    {α : Type*} [Fintype α] (p r : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : (∑ a, p a) = 1)
    (hr_nonneg : ∀ a, 0 ≤ r a) (hr_sum : (∑ a, r a) = 1) :
    |(∑ a, p a ^ 2) - (∑ a, r a ^ 2)| ≤ ∑ a, |p a - r a| := by
  have hdiff_sum : (∑ a, (p a - r a)) = 0 := by
    rw [Finset.sum_sub_distrib, hp_sum, hr_sum]
    norm_num
  calc
    |(∑ a, p a ^ 2) - (∑ a, r a ^ 2)| =
        |∑ a, (p a - r a) * (p a + r a - 1)| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          calc
            (∑ a, (p a ^ 2 - r a ^ 2)) =
                ∑ a, (p a - r a) * (p a + r a) := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  ring
            _ = ∑ a, ((p a - r a) * (p a + r a) - (p a - r a)) := by
                  rw [Finset.sum_sub_distrib, hdiff_sum, sub_zero]
            _ = ∑ a, (p a - r a) * (p a + r a - 1) := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  ring
    _ ≤ ∑ a, |(p a - r a) * (p a + r a - 1)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |p a - r a| := by
          refine Finset.sum_le_sum ?_
          intro a _
          rw [abs_mul]
          have hp_le_one : p a ≤ 1 := by
            calc
              p a ≤ ∑ x, p x := by
                exact Finset.single_le_sum (fun x _ => hp_nonneg x) (Finset.mem_univ a)
              _ = 1 := hp_sum
          have hr_le_one : r a ≤ 1 := by
            calc
              r a ≤ ∑ x, r x := by
                exact Finset.single_le_sum (fun x _ => hr_nonneg x) (Finset.mem_univ a)
              _ = 1 := hr_sum
          have hsum_nonneg : 0 ≤ p a + r a := add_nonneg (hp_nonneg a) (hr_nonneg a)
          have hsum_le_two : p a + r a ≤ 2 := by linarith
          have habs_factor : |p a + r a - 1| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith
          calc
            |p a - r a| * |p a + r a - 1| ≤ |p a - r a| * 1 := by
              exact mul_le_mul_of_nonneg_left habs_factor (abs_nonneg _)
            _ = |p a - r a| := by ring

lemma xi_godel_mod_register_collision_dilution_product_uniform_sum
    {X : Type*} [Fintype X] (q : ℕ) (hq : 2 ≤ q) (w : X → ℝ) :
    (∑ z : X × Fin q, w z.1 / (q : ℝ)) = ∑ x : X, w x := by
  have hq_ne : (q : ℝ) ≠ 0 := by positivity
  calc
    (∑ z : X × Fin q, w z.1 / (q : ℝ)) =
        ∑ x : X, ∑ _j : Fin q, w x / (q : ℝ) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ x : X, w x := by
          refine Finset.sum_congr rfl ?_
          intro x _
          calc
            (∑ _j : Fin q, w x / (q : ℝ)) = (q : ℝ) * (w x / (q : ℝ)) := by
              simp [Finset.sum_const]
            _ = w x := by
              field_simp [hq_ne]

lemma xi_godel_mod_register_collision_dilution_product_uniform_collision
    {X : Type*} [Fintype X] (q : ℕ) (hq : 2 ≤ q) (w : X → ℝ) :
    (∑ z : X × Fin q, (w z.1 / (q : ℝ)) ^ 2) =
      (1 / (q : ℝ)) * (∑ x : X, w x ^ 2) := by
  have hq_ne : (q : ℝ) ≠ 0 := by positivity
  have hq_sq_ne : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_ne
  calc
    (∑ z : X × Fin q, (w z.1 / (q : ℝ)) ^ 2) =
        ∑ x : X, ∑ _j : Fin q, (w x / (q : ℝ)) ^ 2 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ x : X, (w x ^ 2 / (q : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          calc
            (∑ _j : Fin q, (w x / (q : ℝ)) ^ 2) =
                (q : ℝ) * (w x / (q : ℝ)) ^ 2 := by
                  simp [Finset.sum_const]
            _ = w x ^ 2 / (q : ℝ) := by
                  field_simp [hq_ne, hq_sq_ne]
    _ = (1 / (q : ℝ)) * (∑ x : X, w x ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring

/-- Paper label: `prop:xi-godel-mod-register-collision-dilution`. -/
theorem paper_xi_godel_mod_register_collision_dilution {X : Type*} [Fintype X]
    [DecidableEq X] (q : ℕ) (hq : 2 ≤ q) (P : X × Fin q → ℝ) (w : X → ℝ)
    (eps : ℝ) (hP_nonneg : ∀ z, 0 ≤ P z)
    (hP_sum : (∑ z : X × Fin q, P z) = 1) (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_sum : (∑ x : X, w x) = 1)
    (hTV :
      (1 / 2 : ℝ) * (∑ z : X × Fin q, |P z - w z.1 / (q : ℝ)|) ≤ eps) :
    |(∑ z : X × Fin q, P z ^ 2) -
      (1 / (q : ℝ)) * (∑ x : X, w x ^ 2)| ≤ 2 * eps := by
  let U : X × Fin q → ℝ := fun z => w z.1 / (q : ℝ)
  have hq_pos : (0 : ℝ) < q := by positivity
  have hU_nonneg : ∀ z, 0 ≤ U z := by
    intro z
    exact div_nonneg (hw_nonneg z.1) (le_of_lt hq_pos)
  have hU_sum : (∑ z : X × Fin q, U z) = 1 := by
    dsimp [U]
    rw [xi_godel_mod_register_collision_dilution_product_uniform_sum q hq w, hw_sum]
  have hcollision_U :
      (∑ z : X × Fin q, U z ^ 2) =
        (1 / (q : ℝ)) * (∑ x : X, w x ^ 2) := by
    dsimp [U]
    exact xi_godel_mod_register_collision_dilution_product_uniform_collision q hq w
  have hl1_bound :
      |(∑ z : X × Fin q, P z ^ 2) - (∑ z : X × Fin q, U z ^ 2)| ≤
        ∑ z : X × Fin q, |P z - U z| :=
    xi_godel_mod_register_collision_dilution_probability_l2_lipschitz P U hP_nonneg hP_sum
      hU_nonneg hU_sum
  have hl1_le : (∑ z : X × Fin q, |P z - U z|) ≤ 2 * eps := by
    nlinarith [hTV]
  rw [← hcollision_U]
  exact le_trans hl1_bound hl1_le

end

end Omega.Zeta
