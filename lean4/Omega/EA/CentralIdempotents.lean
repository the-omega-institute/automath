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

/-- All four central idempotents are idempotent under involutive hypotheses.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_all_idempotent {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b ^ 2 = epp a b ∧
    epn a b ^ 2 = epn a b ∧
    enp a b ^ 2 = enp a b ∧
    enn a b ^ 2 = enn a b := by
  rcases rat_sq_eq_one_cases ha with rfl | rfl <;>
    rcases rat_sq_eq_one_cases hb with rfl | rfl <;>
    norm_num [epp, epn, enp, enn]

-- ══════════════════════════════════════════════════════════════
-- Phase R285: Individual cross-product zero laws
-- ══════════════════════════════════════════════════════════════

/-- thm:fold-groupoid-z2x2-central-idempotents -/
theorem epp_mul_epn {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b * epn a b = 0 :=
  (central_idempotents_pairwise_orthogonal ha hb).1

/-- thm:fold-groupoid-z2x2-central-idempotents -/
theorem epp_mul_enp {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b * enp a b = 0 :=
  (central_idempotents_pairwise_orthogonal ha hb).2.1

/-- thm:fold-groupoid-z2x2-central-idempotents -/
theorem epp_mul_enn {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b * enn a b = 0 :=
  (central_idempotents_pairwise_orthogonal ha hb).2.2.1

/-- thm:fold-groupoid-z2x2-central-idempotents -/
theorem epn_mul_enp {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epn a b * enp a b = 0 :=
  (central_idempotents_pairwise_orthogonal ha hb).2.2.2.1

/-- thm:fold-groupoid-z2x2-central-idempotents -/
theorem epn_mul_enn {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epn a b * enn a b = 0 :=
  (central_idempotents_pairwise_orthogonal ha hb).2.2.2.2.1

/-- thm:fold-groupoid-z2x2-central-idempotents -/
theorem enp_mul_enn {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    enp a b * enn a b = 0 :=
  (central_idempotents_pairwise_orthogonal ha hb).2.2.2.2.2

/-- Complete system: sum=1, all idempotent, all pairwise orthogonal.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem paper_central_idempotents_complete_system {a b : ℚ}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    (epp a b + epn a b + enp a b + enn a b = 1) ∧
    (epp a b ^ 2 = epp a b) ∧ (epn a b ^ 2 = epn a b) ∧
    (enp a b ^ 2 = enp a b) ∧ (enn a b ^ 2 = enn a b) ∧
    (epp a b * epn a b = 0) ∧ (epp a b * enp a b = 0) ∧
    (epp a b * enn a b = 0) ∧ (epn a b * enp a b = 0) ∧
    (epn a b * enn a b = 0) ∧ (enp a b * enn a b = 0) := by
  exact ⟨central_idempotents_sum_one,
    (central_idempotents_all_idempotent ha hb).1,
    (central_idempotents_all_idempotent ha hb).2.1,
    (central_idempotents_all_idempotent ha hb).2.2.1,
    (central_idempotents_all_idempotent ha hb).2.2.2,
    epp_mul_epn ha hb, epp_mul_enp ha hb, epp_mul_enn ha hb,
    epn_mul_enp ha hb, epn_mul_enn ha hb, enp_mul_enn ha hb⟩

/-- Paper-facing wrapper for the complete central-idempotent package.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem paper_fold_groupoid_z2x2_central_idempotents {a b : ℚ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    epp a b + epn a b + enp a b + enn a b = 1 ∧ epp a b ^ 2 = epp a b ∧
    epn a b ^ 2 = epn a b ∧ enp a b ^ 2 = enp a b ∧ enn a b ^ 2 = enn a b ∧
    epp a b * epn a b = 0 ∧ epp a b * enp a b = 0 ∧ epp a b * enn a b = 0 ∧
    epn a b * enp a b = 0 ∧ epn a b * enn a b = 0 ∧ enp a b * enn a b = 0 := by
  exact paper_central_idempotents_complete_system ha hb

/-- Central idempotents at (+1, +1): only epp activates.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_at_one_one :
    epp 1 1 = 1 ∧ epn 1 1 = 0 ∧ enp 1 1 = 0 ∧ enn 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [epp, epn, enp, enn]

/-- Central idempotents at (+1, -1): only epn activates.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_at_one_neg_one :
    epp 1 (-1) = 0 ∧ epn 1 (-1) = 1 ∧
    enp 1 (-1) = 0 ∧ enn 1 (-1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [epp, epn, enp, enn]

/-- Central idempotents at (-1, +1): only enp activates.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_at_neg_one_one :
    epp (-1) 1 = 0 ∧ epn (-1) 1 = 0 ∧
    enp (-1) 1 = 1 ∧ enn (-1) 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [epp, epn, enp, enn]

/-- Central idempotents at (-1, -1): only enn activates.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem central_idempotents_at_neg_one_neg_one :
    epp (-1) (-1) = 0 ∧ epn (-1) (-1) = 0 ∧
    enp (-1) (-1) = 0 ∧ enn (-1) (-1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [epp, epn, enp, enn]

/-- Paper-facing four-corner witness table for the central idempotents.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem paper_central_idempotents_four_corner_witness :
    (epp 1 1 = 1 ∧ epn 1 1 = 0 ∧ enp 1 1 = 0 ∧ enn 1 1 = 0) ∧
    (epp 1 (-1) = 0 ∧ epn 1 (-1) = 1 ∧ enp 1 (-1) = 0 ∧ enn 1 (-1) = 0) ∧
    (epp (-1) 1 = 0 ∧ epn (-1) 1 = 0 ∧ enp (-1) 1 = 1 ∧ enn (-1) 1 = 0) ∧
    (epp (-1) (-1) = 0 ∧ epn (-1) (-1) = 0 ∧
     enp (-1) (-1) = 0 ∧ enn (-1) (-1) = 1) :=
  ⟨central_idempotents_at_one_one,
   central_idempotents_at_one_neg_one,
   central_idempotents_at_neg_one_one,
   central_idempotents_at_neg_one_neg_one⟩

end Omega.EA
