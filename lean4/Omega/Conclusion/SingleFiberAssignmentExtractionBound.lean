import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

open scoped Classical
open Classical

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- Paper label: `cor:conclusion-single-fiber-assignment-extraction-bound`.
Successful assignment reconstructions inject into the code alphabet through the encoder. -/
theorem paper_conclusion_single_fiber_assignment_extraction_bound {F Code Bits : Type*}
    [Fintype F] [Fintype Code] [Fintype Bits] (E : F → Code) (g : Code → Bits)
    (π : F ≃ Bits) (L : ℕ) (hCode : Fintype.card Code ≤ 2 ^ L) :
    Fintype.card {ω : F // g (E ω) = π ω} ≤ 2 ^ L := by
  have hsuccess_le_code :
      Fintype.card {ω : F // g (E ω) = π ω} ≤ Fintype.card Code := by
    refine Fintype.card_le_of_injective (fun ω : {ω : F // g (E ω) = π ω} => E ω.1) ?_
    intro ω₁ ω₂ hE
    apply Subtype.ext
    apply π.injective
    calc
      π ω₁.1 = g (E ω₁.1) := ω₁.2.symm
      _ = g (E ω₂.1) := congrArg g hE
      _ = π ω₂.1 := ω₂.2
  exact hsuccess_le_code.trans hCode

end Omega.Conclusion
