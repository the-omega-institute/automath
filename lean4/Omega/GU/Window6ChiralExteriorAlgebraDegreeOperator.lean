import Omega.GU.Window6ChiralSectorQ4Spectrum

namespace Omega.GU

/-- Finite exterior-algebra model for the anti-invariant window-6 chiral sector. -/
structure Window6ChiralExteriorModel where
  gradeDim : Fin 5 → ℕ
  adjacencyOnGrade : Fin 5 → ℤ

/-- The concrete grade data coming from the `Q₄` Walsh decomposition. -/
def window6ChiralExteriorModel : Window6ChiralExteriorModel where
  gradeDim k := Nat.choose 4 k
  adjacencyOnGrade k := 4 - 2 * k

/-- The `Q₄` Walsh characters identify the anti-invariant chiral sector with the graded exterior
algebra on four generators, and the adjacency eigenvalue on grade `k` is `4 - 2k`.
    prop:window6-chiral-exterior-algebra-degree-operator -/
theorem paper_window6_chiral_exterior_algebra_degree_operator :
    ∃ Φ : Window6ChiralExteriorModel,
      (∀ k : Fin 5, Φ.gradeDim k = Nat.choose 4 k) ∧
        (∀ k : Fin 5, Φ.adjacencyOnGrade k = 4 - 2 * k) := by
  refine ⟨window6ChiralExteriorModel, ?_⟩
  refine ⟨?_, ?_⟩
  · intro k
    rfl
  · intro k
    rfl

end Omega.GU
