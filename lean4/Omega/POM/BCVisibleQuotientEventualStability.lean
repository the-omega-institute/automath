import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrderIsoNat

namespace Omega.POM

/-- A descending chain of subgroups in a finite group eventually stabilizes.
    thm:pom-bc-visible-quotient-eventual-stability -/
theorem paper_pom_bc_visible_quotient_eventual_stability {G : Type*} [Group G] [Fintype G]
    (N : ℕ → Subgroup G) (hmono : ∀ m, N (m + 1) ≤ N m) :
    ∃ m0 : ℕ, ∀ m ≥ m0, N m = N m0 := by
  let c : ℕ → ℕ := fun m => Nat.card (N m)
  have hcardmono : ∀ m, c (m + 1) ≤ c m := by
    intro m
    exact Subgroup.card_le_of_le (hmono m)
  let chain : ℕ →o OrderDual ℕ :=
    ⟨c, antitone_nat_of_succ_le hcardmono⟩
  obtain ⟨m0, hm0⟩ := WellFoundedGT.monotone_chain_condition chain
  have hanti : Antitone N := antitone_nat_of_succ_le hmono
  refine ⟨m0, ?_⟩
  intro m hm
  have hle : N m ≤ N m0 := hanti hm
  have hcard_ge : Nat.card (N m0) ≤ Nat.card (N m) := by
    simpa [c] using (Eq.ge (hm0 m hm))
  exact Subgroup.eq_of_le_of_card_ge hle hcard_ge

end Omega.POM
