import Mathlib.Tactic

/-- Paper label: `prop:xi-hankel-minimal-sampling-one-point-exception-robust`. -/
theorem paper_xi_hankel_minimal_sampling_one_point_exception_robust
    {detPrev detCurr u uStar eta : ℝ} (hdet : detPrev ≠ 0)
    (hfactor : detCurr = detPrev * (u - uStar)) (heta : 0 ≤ eta)
    (hsep : eta ≤ |u - uStar|) :
    (detCurr = 0 ↔ u = uStar) ∧ eta * |detPrev| ≤ |detCurr| := by
  constructor
  · constructor
    · intro hzero
      have hmul : detPrev * (u - uStar) = 0 := by
        simpa [hfactor] using hzero
      rcases mul_eq_zero.mp hmul with hprev | hdiff
      · exact False.elim (hdet hprev)
      · linarith
    · intro hu
      subst u
      simp [hfactor]
  · have hnonneg : 0 ≤ |detPrev| := abs_nonneg detPrev
    have _heta_abs : 0 ≤ |u - uStar| := le_trans heta hsep
    have hscaled : eta * |detPrev| ≤ |u - uStar| * |detPrev| :=
      mul_le_mul_of_nonneg_right hsep hnonneg
    have habs : |detCurr| = |detPrev| * |u - uStar| := by
      rw [hfactor, abs_mul]
    calc
      eta * |detPrev| ≤ |u - uStar| * |detPrev| := hscaled
      _ = |detPrev| * |u - uStar| := by ring
      _ = |detCurr| := by rw [habs]
