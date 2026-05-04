import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part62dea-prime-adjunction-order-independent-kernel-product`. -/
theorem paper_xi_time_part62dea_prime_adjunction_order_independent_kernel_product
    {α : Type} [DecidableEq α] (S T : Finset α) (hdisj : Disjoint S T) :
    (∀ l : List α, l.Nodup → (∀ p, p ∈ l ↔ p ∈ T) →
        l.foldl (fun U p => insert p U) S = S ∪ T) ∧
      (∀ p, p ∈ S ∪ T ∧ p ∉ S ↔ p ∈ T) := by
  constructor
  · intro l _ hlT
    have hfold :
        ∀ (l : List α) (U : Finset α),
          l.foldl (fun U p => insert p U) U = U ∪ l.toFinset := by
      intro l
      induction l with
      | nil =>
          intro U
          simp
      | cons p ps ih =>
          intro U
          rw [List.foldl, ih]
          ext q
          simp [Finset.mem_union, Finset.mem_insert]
    have htoFinset : l.toFinset = T := by
      ext p
      simpa using hlT p
    rw [hfold, htoFinset]
  · intro p
    constructor
    · intro hp
      rcases hp with ⟨hpUnion, hpNotS⟩
      rcases Finset.mem_union.mp hpUnion with hpS | hpT
      · exact False.elim (hpNotS hpS)
      · exact hpT
    · intro hpT
      exact
        ⟨Finset.mem_union.mpr (Or.inr hpT),
          fun hpS => (Finset.disjoint_left.mp hdisj hpS hpT).elim⟩

end Omega.Zeta
