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

/-- Real-kernel conjugation on the critical-line parametrization specializes the parity sign to
the real/imaginary dichotomy.
    cor:conclusion-toyrh-real-kernel-critical-line-real-imaginary-dichotomy -/
theorem paper_conclusion_toyrh_real_kernel_critical_line_real_imaginary_dichotomy {α K : Type*}
    [Field K] (Xi : α → K) (ι : α → α) (conjK : K → K) (line : Int → α) (eps : K)
    (hreal : ∀ t, conjK (Xi (line t)) = Xi (ι (line t)))
    (hparity : ∀ t, Xi (ι (line t)) = eps * Xi (line t)) :
    (eps = 1 → ∀ t, conjK (Xi (line t)) = Xi (line t)) ∧
      (eps = -1 → ∀ t, conjK (Xi (line t)) = -Xi (line t)) := by
  constructor
  · intro heps t
    calc
      conjK (Xi (line t)) = Xi (ι (line t)) := hreal t
      _ = eps * Xi (line t) := hparity t
      _ = Xi (line t) := by simp [heps]
  · intro heps t
    calc
      conjK (Xi (line t)) = Xi (ι (line t)) := hreal t
      _ = eps * Xi (line t) := hparity t
      _ = -Xi (line t) := by simp [heps]

end Omega.Conclusion
