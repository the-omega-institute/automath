import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-j-sextic-elliptic-lattes-postcritical-tree-levels`. -/
theorem paper_xi_j_sextic_elliptic_lattes_postcritical_tree_levels {α : Type*}
    [DecidableEq α] (n : ℕ) (hn : 1 ≤ n) (Pinf P1 P2 P3 : Finset α)
    (hInf : Pinf.card = 2 ^ (2 * n - 1) + 2) (h1 : P1.card = 2 ^ (2 * n - 1))
    (h2 : P2.card = 2 ^ (2 * n - 1)) (h3 : P3.card = 2 ^ (2 * n - 1))
    (hd01 : Disjoint Pinf P1) (hd02 : Disjoint Pinf P2) (hd03 : Disjoint Pinf P3)
    (hd12 : Disjoint P1 P2) (hd13 : Disjoint P1 P3) (hd23 : Disjoint P2 P3) :
    (Pinf ∪ P1 ∪ P2 ∪ P3).card = 2 ^ (2 * n + 1) + 2 := by
  have hd012 : Disjoint (Pinf ∪ P1) P2 := by
    rw [Finset.disjoint_union_left]
    exact ⟨hd02, hd12⟩
  have hd0123 : Disjoint (Pinf ∪ P1 ∪ P2) P3 := by
    rw [Finset.disjoint_union_left]
    exact ⟨by
      rw [Finset.disjoint_union_left]
      exact ⟨hd03, hd13⟩, hd23⟩
  have hcard :
      (Pinf ∪ P1 ∪ P2 ∪ P3).card =
        Pinf.card + P1.card + P2.card + P3.card := by
    calc
      (Pinf ∪ P1 ∪ P2 ∪ P3).card = (Pinf ∪ P1 ∪ P2).card + P3.card := by
        exact Finset.card_union_of_disjoint hd0123
      _ = ((Pinf ∪ P1).card + P2.card) + P3.card := by
        rw [Finset.card_union_of_disjoint hd012]
      _ = (Pinf.card + P1.card + P2.card) + P3.card := by
        rw [Finset.card_union_of_disjoint hd01]
      _ = Pinf.card + P1.card + P2.card + P3.card := by omega
  have hpow :
      2 ^ (2 * n + 1) = 4 * 2 ^ (2 * n - 1) := by
    have hshift : 2 * n + 1 = (2 * n - 1) + 2 := by omega
    rw [hshift, pow_add]
    ring
  rw [hcard, hInf, h1, h2, h3, hpow]
  ring

end Omega.Zeta
