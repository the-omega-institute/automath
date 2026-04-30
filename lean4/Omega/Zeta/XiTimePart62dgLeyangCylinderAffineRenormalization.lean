import Mathlib.Data.Set.Lattice

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dg-leyang-cylinder-affine-renormalization`. -/
theorem paper_xi_time_part62dg_leyang_cylinder_affine_renormalization {α β : Type*}
    (cyl : Fin 5 → ℕ → Set α) (branch : Fin 5 → ℕ → Set β) (proj : ℕ → α → β)
    (Ψ : ℕ → ℕ → α → α) (L : ℕ)
    (hproj : ∀ i n, Set.image (proj n) (cyl i n) = branch i n)
    (hmap : ∀ r k i n, Set.image (Ψ r k) (cyl i n) = cyl i (n + L * k)) :
    (∀ i n, Set.image (proj n) (cyl i n) = branch i n) ∧
      (∀ r k n, Set.image (Ψ r k) (⋃ i, cyl i n) = ⋃ i, cyl i (n + L * k)) := by
  refine ⟨hproj, ?_⟩
  intro r k n
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [← hmap r k i n]
    exact ⟨y, hyi, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    rw [← hmap r k i n] at hxi
    rcases hxi with ⟨y, hyi, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hyi⟩, rfl⟩

end Omega.Zeta
