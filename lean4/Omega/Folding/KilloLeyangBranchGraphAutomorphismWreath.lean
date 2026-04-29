import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Folding.KilloLeyangBranchGraphFullSpectrum

namespace Omega.Folding

noncomputable section

/-- Finite proxy for the hypercube automorphism group
`(Z/2Z)^(2n) ⋊ S_(2n)`: a coordinate flip mask together with a coordinate permutation. -/
abbrev killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model (n : ℕ) :=
  (Fin (leyangBranchGraphDimension n) → Bool) × Equiv.Perm (Fin (leyangBranchGraphDimension n))

/-- Wreath-product model for automorphisms of five disjoint hypercube components. -/
abbrev killo_leyang_branch_graph_automorphism_wreath_branch_aut_model (n : ℕ) :=
  (Fin leyangBranchGraphComponentCount →
      killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) ×
    Equiv.Perm (Fin leyangBranchGraphComponentCount)

/-- Hypercube automorphism count `2^(2n) (2n)!`. -/
theorem killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_card (n : ℕ) :
    Fintype.card (killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) =
      2 ^ (leyangBranchGraphDimension n) * Nat.factorial (leyangBranchGraphDimension n) := by
  change Fintype.card ((Fin (leyangBranchGraphDimension n) → Bool) ×
      Equiv.Perm (Fin (leyangBranchGraphDimension n))) =
    2 ^ (leyangBranchGraphDimension n) * Nat.factorial (leyangBranchGraphDimension n)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_perm,
    Fintype.card_fin]

/-- The disjoint-union automorphism wreath model has cardinality `|Aut(Q_(2n))|^5 · 5!`. -/
theorem killo_leyang_branch_graph_automorphism_wreath_branch_aut_card (n : ℕ) :
    Fintype.card (killo_leyang_branch_graph_automorphism_wreath_branch_aut_model n) =
      Fintype.card (killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) ^
          leyangBranchGraphComponentCount *
        Nat.factorial leyangBranchGraphComponentCount := by
  change Fintype.card ((Fin leyangBranchGraphComponentCount →
      killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) ×
      Equiv.Perm (Fin leyangBranchGraphComponentCount)) =
    Fintype.card (killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) ^
        leyangBranchGraphComponentCount *
      Nat.factorial leyangBranchGraphComponentCount
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]

/-- Paper label: `prop:killo-leyang-branch-graph-automorphism-wreath`. Using the previously
established decomposition of the Lee--Yang branch graph into five copies of `Q_(2n)`, the
automorphism model is the wreath product of the hypercube automorphism model with `S_5`, hence the
expected cardinality formula. -/
theorem paper_killo_leyang_branch_graph_automorphism_wreath (n : ℕ) (hn : 1 ≤ n) :
    LeyangBranchGraphFullSpectrum n ∧
      Fintype.card (killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) =
        2 ^ (2 * n) * Nat.factorial (2 * n) ∧
      Fintype.card (killo_leyang_branch_graph_automorphism_wreath_branch_aut_model n) =
        Fintype.card (killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) ^ 5 *
          Nat.factorial 5 ∧
      Fintype.card (killo_leyang_branch_graph_automorphism_wreath_branch_aut_model n) =
        (2 ^ (2 * n) * Nat.factorial (2 * n)) ^ 5 * Nat.factorial 5 := by
  have hSpectrum := paper_killo_leyang_branch_graph_full_spectrum n hn
  have hCube :=
    killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_card n
  have hBranch :=
    killo_leyang_branch_graph_automorphism_wreath_branch_aut_card n
  refine ⟨hSpectrum, ?_, ?_, ?_⟩
  · simpa [leyangBranchGraphDimension] using hCube
  · simpa [leyangBranchGraphComponentCount] using hBranch
  · calc
      Fintype.card (killo_leyang_branch_graph_automorphism_wreath_branch_aut_model n) =
          Fintype.card (killo_leyang_branch_graph_automorphism_wreath_hypercube_aut_model n) ^
              leyangBranchGraphComponentCount *
            Nat.factorial leyangBranchGraphComponentCount := hBranch
      _ =
          (2 ^ (leyangBranchGraphDimension n) * Nat.factorial (leyangBranchGraphDimension n)) ^
              leyangBranchGraphComponentCount *
            Nat.factorial leyangBranchGraphComponentCount := by rw [hCube]
      _ = (2 ^ (2 * n) * Nat.factorial (2 * n)) ^ 5 * Nat.factorial 5 := by
          simp [leyangBranchGraphComponentCount, leyangBranchGraphDimension]

end

end Omega.Folding
