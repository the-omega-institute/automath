import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

open scoped Classical
open Classical

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- Paper label: `prop:conclusion-single-fiber-decoding-bound`.
Every successfully decoded microstate injects into the finite code alphabet, so the number of
successful states is bounded by the code alphabet size. -/
theorem paper_conclusion_single_fiber_decoding_bound {F Code : Type*} [Fintype F] [Fintype Code]
    (E : F → Code) (D : Code → F) {n L : ℕ} (hfiber : Fintype.card F = 2 ^ n)
    (hcode : Fintype.card Code ≤ 2 ^ L) :
    Fintype.card {ω : F // D (E ω) = ω} ≤ 2 ^ L := by
  have _ : Fintype.card F = 2 ^ n := hfiber
  have hsuccess_le_code : Fintype.card {ω : F // D (E ω) = ω} ≤ Fintype.card Code := by
    refine Fintype.card_le_of_injective (fun ω : {ω : F // D (E ω) = ω} => E ω.1) ?_
    intro ω₁ ω₂ hE
    apply Subtype.ext
    calc
      ω₁.1 = D (E ω₁.1) := ω₁.2.symm
      _ = D (E ω₂.1) := congrArg D hE
      _ = ω₂.1 := ω₂.2
  exact hsuccess_le_code.trans hcode

end Omega.Conclusion
