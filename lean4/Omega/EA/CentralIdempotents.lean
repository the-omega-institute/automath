import Mathlib.Tactic

namespace Omega.EA

def epp (a b : ℚ) : ℚ := ((1 + a) * (1 + b)) / 4
def epn (a b : ℚ) : ℚ := ((1 + a) * (1 - b)) / 4
def enp (a b : ℚ) : ℚ := ((1 - a) * (1 + b)) / 4
def enn (a b : ℚ) : ℚ := ((1 - a) * (1 - b)) / 4

private theorem rat_sq_eq_one_cases {x : ℚ} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have hmul : (x - 1) * (x + 1) = 0 := by
    nlinarith [hx]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with h | h
  · left
    linarith
  · right
    linarith

/-- The ++ central projector is idempotent under involutive hypotheses.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem epp_idempotent {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b ^ 2 = epp a b := by
  rcases rat_sq_eq_one_cases ha with rfl | rfl <;>
    rcases rat_sq_eq_one_cases hb with rfl | rfl <;>
    norm_num [epp]

/-- The four central idempotents sum to one.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_sum_one {a b : ℚ} :
    epp a b + epn a b + enp a b + enn a b = 1 := by
  unfold epp epn enp enn
  ring

/-- The ++ idempotent is orthogonal to the other three under involutive hypotheses.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_orthogonal {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b * epn a b = 0 ∧
    epp a b * enp a b = 0 ∧
    epp a b * enn a b = 0 := by
  rcases rat_sq_eq_one_cases ha with rfl | rfl <;>
    rcases rat_sq_eq_one_cases hb with rfl | rfl <;>
    norm_num [epp, epn, enp, enn]

/-- The four central idempotents are pairwise orthogonal under involutive hypotheses.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_pairwise_orthogonal {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b * epn a b = 0 ∧
    epp a b * enp a b = 0 ∧
    epp a b * enn a b = 0 ∧
    epn a b * enp a b = 0 ∧
    epn a b * enn a b = 0 ∧
    enp a b * enn a b = 0 := by
  rcases rat_sq_eq_one_cases ha with rfl | rfl <;>
    rcases rat_sq_eq_one_cases hb with rfl | rfl <;>
    norm_num [epp, epn, enp, enn]

end Omega.EA
