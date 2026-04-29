import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-gram-shift-positive-pencil-node-spectrum`. -/
theorem paper_xi_gram_shift_positive_pencil_node_spectrum {V : Type*} [AddCommGroup V]
    [Module ℂ V] (G0 G1 A : V →ₗ[ℂ] V) (hG1 : G1 = G0.comp A)
    (hG0_inj : Function.Injective G0) :
    G1 = G0.comp A ∧
      ∀ (lam : ℂ), ((∃ v : V, v ≠ 0 ∧ A v = lam • v) ↔
        ∃ v : V, v ≠ 0 ∧ G1 v = lam • G0 v) := by
  refine ⟨hG1, ?_⟩
  intro lam
  constructor
  · rintro ⟨v, hv_ne, hv⟩
    refine ⟨v, hv_ne, ?_⟩
    rw [hG1]
    change G0 (A v) = lam • G0 v
    rw [hv]
    simp
  · rintro ⟨v, hv_ne, hv⟩
    refine ⟨v, hv_ne, ?_⟩
    apply hG0_inj
    rw [map_smul]
    rw [← hv]
    rw [hG1]
    rfl

end Omega.Zeta
