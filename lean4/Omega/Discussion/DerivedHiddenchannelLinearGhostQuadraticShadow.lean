import Mathlib.Tactic

namespace Omega.Discussion

/-- The hidden dominant character contributes a single linear ghost term. -/
def derived_hiddenchannel_linear_ghost_quadratic_shadow_character_weight
    (η : ℚ) (n : ℕ) : ℚ :=
  η ^ n / (n + 1)

/-- The linear hidden statistic extracted from the same character. -/
def derived_hiddenchannel_linear_ghost_quadratic_shadow_linear_statistic
    (c η : ℚ) (n : ℕ) : ℚ :=
  c * derived_hiddenchannel_linear_ghost_quadratic_shadow_character_weight η n

/-- The KL shadow decays with the squared hidden ratio. -/
def derived_hiddenchannel_linear_ghost_quadratic_shadow_kl_shadow
    (lambda1 η : ℚ) (n : ℕ) : ℚ :=
  (η / lambda1) ^ (2 * n)

private lemma derived_hiddenchannel_linear_ghost_quadratic_shadow_pow_div
    (η lambda1 : ℚ) (n : ℕ) :
    (η / lambda1) ^ n = η ^ n / lambda1 ^ n := by
  rw [div_eq_mul_inv, mul_pow, div_eq_mul_inv, inv_pow]

/-- Paper label: `thm:derived-hiddenchannel-linear-ghost-quadratic-shadow`.
The same hidden character controls the linear ghost statistic and the quadratic KL shadow. -/
theorem paper_derived_hiddenchannel_linear_ghost_quadratic_shadow
    (c lambda1 η : ℚ) (n : ℕ) (hc : c ≠ 0) (hlambda1 : lambda1 ≠ 0) :
    derived_hiddenchannel_linear_ghost_quadratic_shadow_linear_statistic c η n =
        c * derived_hiddenchannel_linear_ghost_quadratic_shadow_character_weight η n ∧
      derived_hiddenchannel_linear_ghost_quadratic_shadow_kl_shadow lambda1 η n =
        (η / lambda1) ^ (2 * n) ∧
      derived_hiddenchannel_linear_ghost_quadratic_shadow_kl_shadow lambda1 η n =
        ((((n + 1 : ℚ) *
            derived_hiddenchannel_linear_ghost_quadratic_shadow_linear_statistic c η n) /
          (c * lambda1 ^ n)) ^ 2) := by
  have hnp1 : (n + 1 : ℚ) ≠ 0 := by positivity
  have hratio :
      (((n + 1 : ℚ) * derived_hiddenchannel_linear_ghost_quadratic_shadow_linear_statistic c η n) /
          (c * lambda1 ^ n)) =
        (η / lambda1) ^ n := by
    unfold derived_hiddenchannel_linear_ghost_quadratic_shadow_linear_statistic
      derived_hiddenchannel_linear_ghost_quadratic_shadow_character_weight
    rw [derived_hiddenchannel_linear_ghost_quadratic_shadow_pow_div]
    field_simp [hc, hlambda1, hnp1]
  refine ⟨rfl, rfl, ?_⟩
  calc
    derived_hiddenchannel_linear_ghost_quadratic_shadow_kl_shadow lambda1 η n
        = (η / lambda1) ^ (n + n) := by
            simp [derived_hiddenchannel_linear_ghost_quadratic_shadow_kl_shadow, two_mul]
    _ = ((η / lambda1) ^ n) ^ 2 := by rw [pow_add, sq]
    _ = ((((n + 1 : ℚ) *
            derived_hiddenchannel_linear_ghost_quadratic_shadow_linear_statistic c η n) /
          (c * lambda1 ^ n)) ^ 2) := by rw [← hratio]

end Omega.Discussion
