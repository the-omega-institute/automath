import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-prime-register-minimal-ideal-left-zero-band`. -/
theorem paper_xi_prime_register_minimal_ideal_left_zero_band (n : ℕ) (hn : 0 < n) :
    (∀ f : Fin n → Fin n, Fintype.card (Set.range f) = 1 ↔
      ∃ a : Fin n, f = fun _ => a) ∧
      (∀ a b : Fin n, ((fun _ : Fin n => a) ∘ (fun _ : Fin n => b)) =
        fun _ => a) ∧
      (∀ I : (Fin n → Fin n) → Prop, (∃ f, I f) →
        (∀ f, I f → ∀ g, I (g ∘ f) ∧ I (f ∘ g)) → ∀ a : Fin n, I (fun _ => a)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro f
    constructor
    · intro hcard
      rcases Fintype.card_eq_one_iff.mp hcard with ⟨y, hy⟩
      refine ⟨y.1, ?_⟩
      funext x
      have hx : (⟨f x, ⟨x, rfl⟩⟩ : Set.range f) = y := hy _
      exact congrArg Subtype.val hx
    · rintro ⟨a, rfl⟩
      have hrange : Set.range (fun _ : Fin n => a) = {a} := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          simp
        · intro hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨⟨0, hn⟩, rfl⟩
      simp [hrange]
  · intro a b
    funext x
    rfl
  · intro I hI hideal a
    rcases hI with ⟨f, hf⟩
    exact (by simpa [Function.comp] using (hideal f hf (fun _ : Fin n => a)).1)

end Omega.Zeta
