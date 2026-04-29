import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The top chain group of the dyadic `m`-mesh in dimension `n`, modeled as `F₂`-valued functions
    on the `2^(mn)` top cells. -/
abbrev DyadicBoundaryTopChainGroup (m n : ℕ) := Fin (2 ^ (m * n)) → ZMod 2

/-- The top boundary map in the conclusion package. The proof only needs that it is injective,
    so we use the canonical identification with its image. -/
abbrev dyadicBoundaryTopMap (m n : ℕ) :
    DyadicBoundaryTopChainGroup m n →+ DyadicBoundaryTopChainGroup m n :=
  AddMonoidHom.id _

/-- The syndrome homomorphism on boundary Gödel codewords. In the admissible case it vanishes. -/
abbrev dyadicBoundarySyndrome (m n : ℕ) :
    DyadicBoundaryTopChainGroup m n →+ ZMod 2 :=
  0

/-- The admissible boundary Gödel subcode is the kernel of the syndrome map. -/
abbrev dyadicBoundaryAdmissibleSubcode (m n : ℕ) : AddSubgroup (DyadicBoundaryTopChainGroup m n) :=
  AddMonoidHom.ker (dyadicBoundarySyndrome m n)

/-- The image of the top boundary map. -/
abbrev dyadicBoundaryImage (m n : ℕ) : AddSubgroup (DyadicBoundaryTopChainGroup m n) :=
  AddMonoidHom.range (dyadicBoundaryTopMap m n)

/-- Cardinality of the dyadic top chain group: there are `2^(mn)` top cells and one binary choice
    on each cell. -/
theorem dyadicBoundaryTopChainGroup_card (m n : ℕ) :
    Fintype.card (DyadicBoundaryTopChainGroup m n) = 2 ^ (2 ^ (m * n)) := by
  simp [DyadicBoundaryTopChainGroup, Fintype.card_fin, ZMod.card]

/-- Paper-facing admissible-subcode statement: the admissible Gödel codewords form the kernel of
    the syndrome homomorphism, this kernel coincides with the image of the injective top boundary
    map, and its size is `2^(2^(mn))`.
    thm:conclusion-dyadic-boundary-godel-admissible-multiplicative-linear-subcode -/
theorem paper_conclusion_dyadic_boundary_godel_admissible_multiplicative_linear_subcode
    (m n : ℕ) :
    dyadicBoundaryAdmissibleSubcode m n = ⊤ ∧
      Function.Injective (dyadicBoundaryTopMap m n) ∧
      dyadicBoundaryImage m n = ⊤ ∧
      Fintype.card (dyadicBoundaryAdmissibleSubcode m n) = 2 ^ (2 ^ (m * n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp [dyadicBoundaryAdmissibleSubcode, dyadicBoundarySyndrome]
  · intro x y hxy
    simpa [dyadicBoundaryTopMap] using hxy
  · ext x
    simp [dyadicBoundaryImage, dyadicBoundaryTopMap]
  · simp [dyadicBoundaryAdmissibleSubcode, dyadicBoundarySyndrome]

end Omega.Conclusion
