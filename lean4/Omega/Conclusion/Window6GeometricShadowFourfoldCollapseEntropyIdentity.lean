import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-geometric-shadow-fourfold-collapse-entropy-identity`.
The uniform four-to-one fiber hypothesis packages the exact shadow collapse, and the entropy
deficit is the concrete identity `log 4 = 2 log 2`. -/
theorem paper_conclusion_window6_geometric_shadow_fourfold_collapse_entropy_identity
    (res : Fin 8 → Fin 2)
    (hfiber : ∀ y : Fin 2, Fintype.card {x : Fin 8 // res x = y} = 4) :
    (∀ y : Fin 2, Fintype.card {x : Fin 8 // res x = y} = 4) ∧
      ∃ ΔS : ℝ, ΔS = Real.log (4 : ℝ) ∧ ΔS = 2 * Real.log 2 := by
  refine ⟨hfiber, ?_⟩
  refine ⟨Real.log (4 : ℝ), rfl, ?_⟩
  calc
    Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
    _ = Real.log (2 : ℝ) + Real.log (2 : ℝ) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    _ = 2 * Real.log 2 := by ring

end Omega.Conclusion
