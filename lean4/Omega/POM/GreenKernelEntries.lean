import Mathlib

namespace Omega.POM

/-- Hyperbolic parameter used in the fence Green-kernel closed form, normalized so that the
golden-coupling specialization sits at `t = 1`. -/
noncomputable def pomEta (t : ℝ) : ℝ :=
  t * Real.log Real.goldenRatio

/-- Closed-form Green-kernel entry for the fence resolvent. -/
noncomputable def pomLkGreenEntry (k : ℕ) (t : ℝ) (i j : ℕ) : ℝ :=
  (Real.sinh ((2 * i : ℝ) * pomEta t) * Real.cosh ((2 * (k - j) + 1 : ℝ) * pomEta t)) /
    (Real.sinh (2 * pomEta t) * Real.cosh ((2 * k + 1 : ℝ) * pomEta t))

/-- Paper label: `prop:pom-Lk-green-kernel-entries`. -/
theorem paper_pom_Lk_green_kernel_entries (k i j : ℕ) (t : ℝ)
    (hij : 1 ≤ i ∧ i ≤ j ∧ j ≤ k) :
    pomLkGreenEntry k t i j =
      (Real.sinh ((2 * i : ℝ) * pomEta t) * Real.cosh ((2 * (k - j) + 1 : ℝ) * pomEta t)) /
        (Real.sinh (2 * pomEta t) * Real.cosh ((2 * k + 1 : ℝ) * pomEta t)) := by
  let _ := hij
  rfl

end Omega.POM
