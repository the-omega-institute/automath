import Mathlib

namespace Omega.Conclusion

/-- The nonempty subset choices on a single boundary layer. -/
def conclusion_coordinate_bundle_kirchhoff_complete_factorization_nonemptySubsets
    {Edge : Type*} [DecidableEq Edge] (s : Finset Edge) : Finset (Finset Edge) :=
  s.powerset.erase ∅

/-- Weight carried by a chosen subset of edges. -/
def conclusion_coordinate_bundle_kirchhoff_complete_factorization_blockWeight
    {Edge : Type*} (z : Edge → ℝ) (B : Finset Edge) : ℝ :=
  B.prod z

/-- Partition function obtained by choosing one nonempty subset in every boundary layer. -/
def conclusion_coordinate_bundle_kirchhoff_complete_factorization_partitionFunction
    {A Edge : Type*} [Fintype A] [DecidableEq A] [DecidableEq Edge]
    (E : A → Finset Edge) (z : Edge → ℝ) : ℝ :=
  ∑ B ∈ Fintype.piFinset
      (fun a => conclusion_coordinate_bundle_kirchhoff_complete_factorization_nonemptySubsets
        (E a)),
    Finset.univ.prod
      (fun a => conclusion_coordinate_bundle_kirchhoff_complete_factorization_blockWeight z (B a))

/-- Minimal exactifications pick exactly one edge in every boundary layer. -/
def conclusion_coordinate_bundle_kirchhoff_complete_factorization_minimalFunction
    {A Edge : Type*} [Fintype A] [DecidableEq A] (E : A → Finset Edge) (z : Edge → ℝ) : ℝ :=
  ∑ b ∈ Fintype.piFinset E, Finset.univ.prod fun a => z (b a)

/-- Paper label: `thm:conclusion-coordinate-bundle-kirchhoff-complete-factorization`.
The exactification partition function factorizes blockwise over nonempty subset choices, and the
minimal exactifications are obtained by forcing a singleton choice in each block. -/
theorem paper_conclusion_coordinate_bundle_kirchhoff_complete_factorization :
    ∀ {A Edge : Type*} [Fintype A] [DecidableEq A] [DecidableEq Edge]
      (E : A → Finset Edge) (z : Edge → ℝ),
      (conclusion_coordinate_bundle_kirchhoff_complete_factorization_partitionFunction E z =
          Finset.univ.prod
            (fun a =>
              ∑ B in
                conclusion_coordinate_bundle_kirchhoff_complete_factorization_nonemptySubsets
                  (E a),
                conclusion_coordinate_bundle_kirchhoff_complete_factorization_blockWeight z B)) ∧
        conclusion_coordinate_bundle_kirchhoff_complete_factorization_minimalFunction E z =
          Finset.univ.prod (fun a => ∑ e in E a, z e) := by
  intro A Edge _ _ E z
  refine ⟨?_, ?_⟩
  · unfold conclusion_coordinate_bundle_kirchhoff_complete_factorization_partitionFunction
    symm
    simpa [conclusion_coordinate_bundle_kirchhoff_complete_factorization_blockWeight] using
      (Finset.prod_univ_sum fun a (B : Finset Edge) =>
        conclusion_coordinate_bundle_kirchhoff_complete_factorization_blockWeight z B)
  · unfold conclusion_coordinate_bundle_kirchhoff_complete_factorization_minimalFunction
    symm
    simpa using Finset.prod_univ_sum fun a (e : Edge) => z e

end Omega.Conclusion
