import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-ground-support-irreversibility`. A directed edge
present in one direction but absent in the reverse direction contradicts detailed balance when the
source has positive stationary mass. -/
theorem paper_conclusion_realinput40_ground_support_irreversibility
    (Q : Fin 4 → Fin 4 → ℝ) (π : Fin 4 → ℝ)
    (hπ2 : 0 < π ⟨1, by decide⟩)
    (hQ23 : 0 < Q ⟨1, by decide⟩ ⟨2, by decide⟩)
    (hQ32 : Q ⟨2, by decide⟩ ⟨1, by decide⟩ = 0)
    (hDetailed :
      π ⟨1, by decide⟩ * Q ⟨1, by decide⟩ ⟨2, by decide⟩ =
        π ⟨2, by decide⟩ * Q ⟨2, by decide⟩ ⟨1, by decide⟩) :
    False := by
  have hleft_pos : 0 < π ⟨1, by decide⟩ * Q ⟨1, by decide⟩ ⟨2, by decide⟩ :=
    mul_pos hπ2 hQ23
  have hright_zero :
      π ⟨2, by decide⟩ * Q ⟨2, by decide⟩ ⟨1, by decide⟩ = 0 := by
    rw [hQ32, mul_zero]
  have hleft_zero : π ⟨1, by decide⟩ * Q ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 :=
    hDetailed.trans hright_zero
  exact (ne_of_gt hleft_pos) hleft_zero

end Omega.Conclusion
