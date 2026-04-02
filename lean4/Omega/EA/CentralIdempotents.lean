import Mathlib.Tactic

namespace Omega.EA

def epp (a b : ℚ) : ℚ := ((1 + a) * (1 + b)) / 4
def epn (a b : ℚ) : ℚ := ((1 + a) * (1 - b)) / 4
def enp (a b : ℚ) : ℚ := ((1 - a) * (1 + b)) / 4
def enn (a b : ℚ) : ℚ := ((1 - a) * (1 - b)) / 4

/-- The ++ central projector is idempotent under involutive hypotheses.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem epp_idempotent {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b ^ 2 = epp a b := by
  unfold epp
  have ha1 : (1 + a) ^ 2 = 2 * (1 + a) := by
    calc
      (1 + a) ^ 2 = 1 + 2 * a + a ^ 2 := by ring
      _ = 2 * (1 + a) := by rw [ha]; ring
  have hb1 : (1 + b) ^ 2 = 2 * (1 + b) := by
    calc
      (1 + b) ^ 2 = 1 + 2 * b + b ^ 2 := by ring
      _ = 2 * (1 + b) := by rw [hb]; ring
  rw [div_pow, ha1, hb1]
  ring

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
  constructor
  · unfold epp epn
    have hb0 : (1 - b) * (1 + b) = 0 := by
      calc
        (1 - b) * (1 + b) = 1 - b ^ 2 := by ring
        _ = 0 := by rw [hb]
    field_simp
    rw [mul_assoc, hb0]
    ring
  constructor
  · unfold epp enp
    have ha0 : (1 - a) * (1 + a) = 0 := by
      calc
        (1 - a) * (1 + a) = 1 - a ^ 2 := by ring
        _ = 0 := by rw [ha]
    field_simp
    rw [show (1 + a) * (1 - a) = 0 by rw [mul_comm, ha0]]
    ring
  · unfold epp enn
    have ha0 : (1 - a) * (1 + a) = 0 := by
      calc
        (1 - a) * (1 + a) = 1 - a ^ 2 := by ring
        _ = 0 := by rw [ha]
    field_simp
    rw [mul_assoc, show (1 + a) * (1 - a) = 0 by rw [mul_comm, ha0]]
    ring

end Omega.EA
