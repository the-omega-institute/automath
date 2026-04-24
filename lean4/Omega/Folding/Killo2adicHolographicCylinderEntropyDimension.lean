import Mathlib
import Omega.Folding.Killo2adicHolographicAttractorDimension

namespace Omega.Folding

open Filter
open scoped Topology

noncomputable section

/-- The cylinder entropy quotient specialized to the exact constant branch-count model. -/
noncomputable def killo_2adic_holographic_cylinder_entropy_dimension_quotient
    (L q : ℕ) (_n : ℕ) : ℝ :=
  Real.log q / ((L : ℝ) * Real.log 2)

/-- Paper label: `thm:killo-2adic-holographic-cylinder-entropy-dimension`. In the constant
prefix-count model the cylinder entropy quotient is independent of the level, so its limit is the
same closed form. -/
theorem paper_killo_2adic_holographic_cylinder_entropy_dimension
    {L q : ℕ} (_hL : 0 < L) :
    (∀ n : ℕ,
      killo_2adic_holographic_cylinder_entropy_dimension_quotient L q n =
        Real.log q / ((L : ℝ) * Real.log 2)) ∧
      Tendsto (killo_2adic_holographic_cylinder_entropy_dimension_quotient L q) atTop
        (nhds (Real.log q / ((L : ℝ) * Real.log 2))) ∧
      killo_2adic_holographic_attractor_dimension_value (2 ^ L) q = Real.logb (2 ^ L) q := by
  refine ⟨?_, ?_⟩
  · intro n
    rfl
  · refine ⟨?_, ?_⟩
    · have hconst :
          killo_2adic_holographic_cylinder_entropy_dimension_quotient L q =
            fun _ : ℕ => Real.log q / ((L : ℝ) * Real.log 2) := by
          funext n
          rfl
      rw [hconst]
      exact tendsto_const_nhds
    · simp [killo_2adic_holographic_attractor_dimension_value]

end

end Omega.Folding
