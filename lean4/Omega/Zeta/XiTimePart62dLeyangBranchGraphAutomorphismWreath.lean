import Mathlib.Data.Fintype.Perm
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace

namespace Omega.Zeta

/-- Coordinate flips of the `2n`-dimensional hypercube. -/
abbrev xiHypercubeCoordinateFlips (n : ℕ) :=
  Fin (2 * n) → Fin 2

/-- The standard hyperoctahedral model `(\mathbb Z/2\mathbb Z)^(2n) ⋊ S_(2n)` for
`Aut(Q_(2n))`. -/
abbrev xiHypercubeAutomorphismModel (n : ℕ) :=
  xiHypercubeCoordinateFlips n × Equiv.Perm (Fin (2 * n))

/-- The Lee--Yang branch graph has five connected hypercube components, so its automorphism model
is the componentwise hypercube automorphism data together with a permutation of the five
components. -/
abbrev xiLeyangBranchGraphAutomorphismModel (n : ℕ) :=
  (Fin 5 → xiHypercubeAutomorphismModel n) × Equiv.Perm (Fin 5)

/-- The `G_n` branch graph is the disjoint union of five copies of `Q_(2n)`, hence its
automorphism group is the wreath-product model
`Aut(Q_(2n))^5 ⋊ S_5 = ((\mathbb Z/2\mathbb Z)^(2n) ⋊ S_(2n)) ≀ S_5`.
    thm:xi-time-part62d-leyang-branch-graph-automorphism-wreath -/
theorem paper_xi_time_part62d_leyang_branch_graph_automorphism_wreath (n : ℕ) :
    (∀ j ∈ Finset.range (2 * n + 1),
      leyangBranchsetMultiplicity n j = 5 * Nat.choose (2 * n) j) ∧
      Nonempty
        (xiLeyangBranchGraphAutomorphismModel n ≃
          (Fin 5 → ((Fin (2 * n) → Fin 2) × Equiv.Perm (Fin (2 * n)))) ×
            Equiv.Perm (Fin 5)) ∧
      Fintype.card (xiHypercubeAutomorphismModel n) = 2 ^ (2 * n) * Nat.factorial (2 * n) ∧
      Fintype.card (xiLeyangBranchGraphAutomorphismModel n) =
        (2 ^ (2 * n) * Nat.factorial (2 * n)) ^ 5 * Nat.factorial 5 := by
  have hSingleCard :
      Fintype.card (xiHypercubeAutomorphismModel n) = 2 ^ (2 * n) * Nat.factorial (2 * n) := by
    simp [xiHypercubeAutomorphismModel, xiHypercubeCoordinateFlips, Fintype.card_perm]
  have hBranchCard :
      Fintype.card (xiLeyangBranchGraphAutomorphismModel n) =
        (2 ^ (2 * n) * Nat.factorial (2 * n)) ^ 5 * Nat.factorial 5 := by
    calc
      Fintype.card (xiLeyangBranchGraphAutomorphismModel n)
          = Fintype.card (Fin 5 → xiHypercubeAutomorphismModel n) *
              Fintype.card (Equiv.Perm (Fin 5)) := by
                simp [xiLeyangBranchGraphAutomorphismModel]
      _ = Fintype.card (xiHypercubeAutomorphismModel n) ^ 5 * Nat.factorial 5 := by
            simp [Fintype.card_perm]
      _ = (2 ^ (2 * n) * Nat.factorial (2 * n)) ^ 5 * Nat.factorial 5 := by
            rw [hSingleCard]
  refine ⟨?_, ⟨Equiv.refl _⟩, hSingleCard, hBranchCard⟩
  intro j hj
  simp [leyangBranchsetMultiplicity]

end Omega.Zeta
