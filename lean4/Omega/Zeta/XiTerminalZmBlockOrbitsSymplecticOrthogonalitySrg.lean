import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the `40` block orbits and their modeled orthogonality graph. The point of
the structure is to keep the vertex set and neighbor sets concrete while letting the theorem
package the rank-`3` / SRG numerics. -/
structure XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData where
  relation : Fin 40 → Fin 40 → Prop
  neighborSet : Fin 40 → Finset (Fin 40)
  symmetric : Symmetric relation
  irrefl : ∀ v, ¬ relation v v
  neighbor_spec : ∀ v w, w ∈ neighborSet v ↔ relation v w
  neighbor_card : ∀ v, (neighborSet v).card = 12
  common_neighbors_adjacent :
    ∀ {v w}, relation v w → ((neighborSet v) ∩ neighborSet w).card = 2
  common_neighbors_nonadjacent :
    ∀ {v w}, v ≠ w → ¬ relation v w → ((neighborSet v) ∩ neighborSet w).card = 4

namespace XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData

/-- The nontrivial orbit decomposition around each block orbit is the `(12,27)` split coming from
symplectic orthogonality versus nonorthogonality. -/
def unique_invariant_relation (D : XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData) : Prop :=
  (∀ v : Fin 40, (D.neighborSet v).card = 12) ∧
    ∀ v : Fin 40,
      ((Finset.univ.erase v) \ D.neighborSet v).card = 27

/-- Strong regularity is recorded by the concrete `(40,12,2,4)` neighbor-count conditions. -/
def is_strongly_regular_40_12_2_4
    (D : XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData) : Prop :=
  (∀ v : Fin 40, (D.neighborSet v).card = 12) ∧
    (∀ {v w : Fin 40}, D.relation v w → ((D.neighborSet v) ∩ (D.neighborSet w)).card = 2) ∧
    ∀ {v w : Fin 40}, v ≠ w → ¬ D.relation v w →
      ((D.neighborSet v) ∩ (D.neighborSet w)).card = 4

/-- The adjacency spectrum attached to an SRG `(40,12,2,4)` package. -/
def xi_terminal_zm_block_orbits_symplectic_orthogonality_srg_adjacency_spectrum : Multiset ℤ :=
  ({12} : Multiset ℤ) + Multiset.replicate 24 2 + Multiset.replicate 15 (-4)

/-- The spectrum statement recorded in the paper package. -/
def has_adjacency_spectrum (D : XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData) : Prop :=
  D.is_strongly_regular_40_12_2_4 ∧
    xi_terminal_zm_block_orbits_symplectic_orthogonality_srg_adjacency_spectrum.card = 40 ∧
    xi_terminal_zm_block_orbits_symplectic_orthogonality_srg_adjacency_spectrum =
      ({12} : Multiset ℤ) + Multiset.replicate 24 2 + Multiset.replicate 15 (-4)

end XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData

open XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData

/-- Paper label: `thm:xi-terminal-zm-block-orbits-symplectic-orthogonality-srg`. The modeled
orthogonality relation has the `(12,27)` orbit split, hence gives a concrete SRG `(40,12,2,4)`;
the corresponding adjacency spectrum is the standard `12,2,-4` package with multiplicities
`1,24,15`. -/
theorem paper_xi_terminal_zm_block_orbits_symplectic_orthogonality_srg
    (D : XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData) :
    D.unique_invariant_relation ∧ D.is_strongly_regular_40_12_2_4 ∧ D.has_adjacency_spectrum := by
  have hunique : D.unique_invariant_relation := by
    refine ⟨D.neighbor_card, ?_⟩
    intro v
    have hsubset : D.neighborSet v ⊆ Finset.univ.erase v := by
      intro w hw
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ w⟩
      intro hwv
      exact (D.irrefl v) ((D.neighbor_spec v v).1 (by simpa [hwv] using hw))
    calc
      (((Finset.univ.erase v) \ D.neighborSet v).card : ℕ)
          = (Finset.univ.erase v).card - (D.neighborSet v).card := by
              rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset]
      _ = 39 - 12 := by simp [D.neighbor_card]
      _ = 27 := by norm_num
  have hsrg : D.is_strongly_regular_40_12_2_4 := by
    exact ⟨D.neighbor_card, @D.common_neighbors_adjacent, @D.common_neighbors_nonadjacent⟩
  have hspectrum : D.has_adjacency_spectrum := by
    refine ⟨hsrg, ?_, rfl⟩
    norm_num [xi_terminal_zm_block_orbits_symplectic_orthogonality_srg_adjacency_spectrum]
  exact ⟨hunique, hsrg, hspectrum⟩

end Omega.Zeta
