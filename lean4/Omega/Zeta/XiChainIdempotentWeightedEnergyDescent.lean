import Mathlib.Tactic
import Omega.Zeta.XiChainIdempotentStarSaturationComparableGcd

namespace Omega.Zeta

/-- Paper label: `thm:xi-chain-idempotent-weighted-energy-descent`. -/
theorem paper_xi_chain_idempotent_weighted_energy_descent {n : ℕ}
    (F G : Finset (Fin n)) (w : Fin n → ℤ)
    (hpos : ∀ i ∈ G, i ∉ F → 0 < w i) :
    0 ≤ (∑ i ∈ G, w i) - (∑ i ∈ (chainIdempotentProduct F G), w i) ∧
      ((∑ i ∈ G, w i) - (∑ i ∈ (chainIdempotentProduct F G), w i) = 0 ↔
        G ⊆ F) := by
  classical
  rw [chainIdempotentProduct_eq_inter]
  have hinter_sub : F ∩ G ⊆ G := by
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hsum :
      (∑ i ∈ G, w i) - (∑ i ∈ F ∩ G, w i) = ∑ i ∈ G \ (F ∩ G), w i := by
    rw [← Finset.sum_sdiff hinter_sub]
    abel
  have hnonneg : ∀ i ∈ G \ (F ∩ G), 0 ≤ w i := by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hiG, hiNotInter⟩
    exact le_of_lt (hpos i hiG (by
      intro hiF
      exact hiNotInter (Finset.mem_inter.mpr ⟨hiF, hiG⟩)))
  constructor
  · rw [hsum]
    exact Finset.sum_nonneg hnonneg
  · rw [hsum]
    constructor
    · intro hzero i hiG
      by_contra hiF
      have hiDiff : i ∈ G \ (F ∩ G) := by
        exact Finset.mem_sdiff.mpr ⟨hiG, by
          intro hiInter
          exact hiF (Finset.mem_inter.mp hiInter).1⟩
      have hstrict : 0 < ∑ j ∈ G \ (F ∩ G), w j :=
        Finset.sum_pos' hnonneg ⟨i, hiDiff, hpos i hiG hiF⟩
      linarith
    · intro hsubset
      have hempty : G \ (F ∩ G) = ∅ := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_sdiff.mp hi with ⟨hiG, hiNotInter⟩
          exact (hiNotInter (Finset.mem_inter.mpr ⟨hsubset hiG, hiG⟩)).elim
        · intro hi
          simp at hi
      simp [hempty]

end Omega.Zeta
