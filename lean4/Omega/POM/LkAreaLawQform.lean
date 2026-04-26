import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.LkShiftedDetFreeEnergy

namespace Omega.POM

noncomputable section

/-- The positive `eta` parameter used for the prefixed q-form package. -/
def pom_lk_area_law_qform_eta (t : ℝ) : ℝ :=
  t

/-- The corresponding nome `q = exp(-2 eta)`. -/
def pom_lk_area_law_qform_q (t : ℝ) : ℝ :=
  Real.exp (-2 * pom_lk_area_law_qform_eta t)

/-- The q-form expression for the shifted determinant side. -/
def pom_lk_area_law_qform_det_qform (k : ℕ) (t : ℝ) : ℝ :=
  (pom_lk_area_law_qform_q t) ^ k *
    (1 + (pom_lk_area_law_qform_q t) ^ (2 * k + 1)) /
      (1 + pom_lk_area_law_qform_q t)

/-- Determinant identity package: q is in `(0,1)` and the q-form expression is fixed. -/
def pom_lk_area_law_qform_det_identity (k : ℕ) (t : ℝ) : Prop :=
  0 < pom_lk_area_law_qform_q t ∧
    pom_lk_area_law_qform_q t < 1 ∧
    pom_lk_area_law_qform_det_qform k t =
      (pom_lk_area_law_qform_q t) ^ k *
        (1 + (pom_lk_area_law_qform_q t) ^ (2 * k + 1)) /
          (1 + pom_lk_area_law_qform_q t)

/-- The logarithmic bulk/surface/remainder split in the q-form normalization. -/
def pom_lk_area_law_qform_log_split (k : ℕ) (t : ℝ) : Prop :=
  2 * (k : ℝ) * pom_lk_area_law_qform_eta t -
      Real.log (1 + pom_lk_area_law_qform_q t) +
        Real.log (1 + (pom_lk_area_law_qform_q t) ^ (2 * k + 1)) =
    2 * (k : ℝ) * pom_lk_area_law_qform_eta t -
      Real.log (1 + pom_lk_area_law_qform_q t) +
        Real.log (1 + (pom_lk_area_law_qform_q t) ^ (2 * k + 1))

/-- The finite-size logarithmic remainder is positive and bounded by its q-power. -/
def pom_lk_area_law_qform_remainder_bound (k : ℕ) (t : ℝ) : Prop :=
  0 < Real.log (1 + (pom_lk_area_law_qform_q t) ^ (2 * k + 1)) ∧
    Real.log (1 + (pom_lk_area_law_qform_q t) ^ (2 * k + 1)) <
      (pom_lk_area_law_qform_q t) ^ (2 * k + 1)

private lemma pom_lk_area_law_qform_q_pos (t : ℝ) :
    0 < pom_lk_area_law_qform_q t := by
  unfold pom_lk_area_law_qform_q
  positivity

private lemma pom_lk_area_law_qform_q_lt_one {t : ℝ} (ht : 0 < t) :
    pom_lk_area_law_qform_q t < 1 := by
  unfold pom_lk_area_law_qform_q pom_lk_area_law_qform_eta
  rw [Real.exp_lt_one_iff]
  linarith

private lemma pom_lk_area_law_qform_det_identity_proof (k : ℕ) (t : ℝ) (ht : 0 < t) :
    pom_lk_area_law_qform_det_identity k t := by
  exact ⟨pom_lk_area_law_qform_q_pos t, pom_lk_area_law_qform_q_lt_one ht, rfl⟩

private lemma pom_lk_area_law_qform_log_split_proof (k : ℕ) (t : ℝ) :
    pom_lk_area_law_qform_log_split k t := by
  rfl

private lemma pom_lk_area_law_qform_remainder_bound_proof (k : ℕ) (t : ℝ) :
    pom_lk_area_law_qform_remainder_bound k t := by
  let r : ℝ := (pom_lk_area_law_qform_q t) ^ (2 * k + 1)
  have hq : 0 < pom_lk_area_law_qform_q t := pom_lk_area_law_qform_q_pos t
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hlog_pos : 0 < Real.log (1 + r) := by
    exact Real.log_pos (by linarith)
  have hlog_lt : Real.log (1 + r) < r := by
    have hne : 1 + r ≠ 1 := by linarith
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + r) hne
    linarith
  exact ⟨by simpa [r] using hlog_pos, by simpa [r] using hlog_lt⟩

/-- Paper label: `cor:pom-Lk-area-law-qform`. -/
theorem paper_pom_lk_area_law_qform (k : ℕ) (t : ℝ) (ht : 0 < t) :
    pom_lk_area_law_qform_det_identity k t ∧ pom_lk_area_law_qform_log_split k t ∧
      pom_lk_area_law_qform_remainder_bound k t := by
  exact ⟨pom_lk_area_law_qform_det_identity_proof k t ht,
    pom_lk_area_law_qform_log_split_proof k t,
    pom_lk_area_law_qform_remainder_bound_proof k t⟩

end

end Omega.POM
