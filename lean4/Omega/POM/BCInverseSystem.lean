import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- A transition family for the descending BC-visible subgroup tower. -/
abbrev pom_bc_inverse_system_transition_family {G : Type*} [Group G] (N : ℕ → Subgroup G) :=
  ∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ → N m₂ →* N m₁

/-- The subgroup tower forms an inverse system when its transition maps are the obvious inclusion
homomorphisms and they satisfy the usual identity and composition laws. -/
def pom_bc_inverse_system_statement {G : Type*} [Group G] (N : ℕ → Subgroup G) : Prop :=
  ∃ T : pom_bc_inverse_system_transition_family N,
    (∀ m : ℕ, T (m₁ := m) (m₂ := m) le_rfl = MonoidHom.id (N m)) ∧
      ∀ m₁ m₂ m₃ : ℕ, ∀ h12 : m₁ ≤ m₂, ∀ h23 : m₂ ≤ m₃,
        T (Nat.le_trans h12 h23) = (T h12).comp (T h23)

/-- Paper label: `cor:pom-bc-inverse-system`. A descending subgroup chain carries the canonical
inverse-system structure whose transition maps are induced by inclusion. -/
theorem paper_pom_bc_inverse_system {G : Type*} [Group G] (N : ℕ → Subgroup G)
    (hmono : ∀ m, N (m + 1) ≤ N m) : pom_bc_inverse_system_statement N := by
  let hanti : Antitone N := antitone_nat_of_succ_le hmono
  let T : pom_bc_inverse_system_transition_family N := fun {m₁ m₂} h =>
    { toFun := fun x => ⟨x.1, hanti h x.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  refine ⟨T, ?_, ?_⟩
  · intro m
    ext x
    rfl
  · intro m₁ m₂ m₃ h12 h23
    ext x
    rfl

end Omega.POM
