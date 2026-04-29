import Mathlib.Tactic

namespace Omega.Conclusion

/-- `thm:conclusion-toyrh-completion-sign-center-parity` -/
theorem paper_conclusion_toyrh_completion_sign_center_parity {α K : Type*} [Field K]
    (Xi : α → K) (ι : α → α) (C : K) (hC : C ≠ 0) (hι : ∀ s, ι (ι s) = s)
    (hFE : ∀ s, Xi s = C * Xi (ι s)) (hnonzero : ∃ s, Xi s ≠ 0) : C ^ 2 = 1 := by
  have _ : C ≠ 0 := hC
  obtain ⟨s, hs⟩ := hnonzero
  have hfixed : Xi s = C ^ 2 * Xi s := by
    calc
      Xi s = C * Xi (ι s) := hFE s
      _ = C * (C * Xi (ι (ι s))) := by rw [hFE (ι s)]
      _ = C ^ 2 * Xi s := by
        rw [hι s]
        ring
  have hcancel : C ^ 2 * Xi s = 1 * Xi s := by
    simpa [one_mul] using hfixed.symm
  exact mul_right_cancel₀ hs hcancel

end Omega.Conclusion
