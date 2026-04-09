import Mathlib.Tactic

namespace Omega.CircleDimension

variable {G : Type*} [Group G] {A : Type*} [CommGroup A]

/-- A group hom into an abelian group sends commutators to `1`.
    prop:cdim-global-phase-exhaustion -/
theorem comm_in_kernel (f : G →* A) (a b : G) :
    f (a * b * a⁻¹ * b⁻¹) = 1 := by
  simp [map_mul, map_inv]

/-- A group hom into an abelian group is swap-symmetric on products.
    prop:cdim-global-phase-exhaustion -/
theorem hom_comm_swap (f : G →* A) (a b : G) :
    f (a * b) = f (b * a) := by
  rw [map_mul, map_mul, mul_comm]

/-- Uniqueness of the factorisation through a surjective group hom.
    prop:cdim-global-phase-exhaustion -/
theorem factor_unique_of_surjective
    {H : Type*} [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ)
    (f : G →* A) (g₁ g₂ : H →* A)
    (h1 : g₁.comp φ = f) (h2 : g₂.comp φ = f) :
    g₁ = g₂ := by
  ext h
  obtain ⟨x, hx⟩ := hφ h
  rw [← hx]
  have h1' : g₁ (φ x) = f x := by
    have := DFunLike.congr_fun h1 x
    simpa using this
  have h2' : g₂ (φ x) = f x := by
    have := DFunLike.congr_fun h2 x
    simpa using this
  rw [h1', h2']

/-- Restatement: the commutator-in-kernel property as a ∀ statement.
    prop:cdim-global-phase-exhaustion -/
theorem hom_abelian_commutator_trivial (f : G →* A) :
    ∀ a b : G, f (a * b * a⁻¹ * b⁻¹) = 1 := comm_in_kernel f

/-- Paper package: global phase exhaustion — abelian factorisation.
    prop:cdim-global-phase-exhaustion -/
theorem paper_cdim_global_phase_exhaustion :
    (∀ (f : G →* A) (a b : G), f (a * b * a⁻¹ * b⁻¹) = 1) ∧
    (∀ (f : G →* A) (a b : G), f (a * b) = f (b * a)) ∧
    (∀ {H : Type*} [Group H] (φ : G →* H), Function.Surjective φ →
      ∀ (f : G →* A) (g₁ g₂ : H →* A),
        g₁.comp φ = f → g₂.comp φ = f → g₁ = g₂) :=
  ⟨comm_in_kernel,
   hom_comm_swap,
   fun φ hφ f g₁ g₂ h1 h2 => factor_unique_of_surjective φ hφ f g₁ g₂ h1 h2⟩

end Omega.CircleDimension
