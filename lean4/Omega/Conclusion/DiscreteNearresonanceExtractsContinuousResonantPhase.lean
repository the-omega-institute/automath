import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-discrete-nearresonance-extracts-continuous-resonant-phase`. -/
theorem paper_conclusion_discrete_nearresonance_extracts_continuous_resonant_phase
    (discrete continuous : ℕ → ℝ)
    (hdiscrete :
      ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, ∀ j ≥ J, |discrete j - 1| < eps)
    (htransfer :
      ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, ∀ j ≥ J, |discrete j - continuous j| < eps) :
    ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, ∀ j ≥ J, |continuous j - 1| < eps := by
  intro eps heps
  have heps_half : 0 < eps / 2 := by linarith
  rcases hdiscrete (eps / 2) heps_half with ⟨Jd, hJd⟩
  rcases htransfer (eps / 2) heps_half with ⟨Jt, hJt⟩
  refine ⟨max Jd Jt, ?_⟩
  intro j hj
  have hJd_le : Jd ≤ j := le_trans (Nat.le_max_left Jd Jt) hj
  have hJt_le : Jt ≤ j := le_trans (Nat.le_max_right Jd Jt) hj
  have hd : |discrete j - 1| < eps / 2 := hJd j hJd_le
  have ht : |continuous j - discrete j| < eps / 2 := by
    simpa [abs_sub_comm] using hJt j hJt_le
  have htri :
      |continuous j - 1| ≤ |continuous j - discrete j| + |discrete j - 1| := by
    have h :=
      abs_add_le (continuous j - discrete j) (discrete j - 1)
    convert h using 1
    ring_nf
  linarith

end Omega.Conclusion
