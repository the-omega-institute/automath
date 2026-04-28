import Mathlib.Data.Set.Basic

/-!
Finite flux coordinate factorization through an injective coordinate map.
-/

/-- Paper label:
`thm:xi-time-part9xbb-explicit-wulff-finite-flux-coordinate-factorization`. -/
theorem paper_xi_time_part9xbb_explicit_wulff_finite_flux_coordinate_factorization
    {α β γ : Type*} (F : α → β) (I : α → γ) (hF : Function.Injective F) :
    (∃! Φ : Set.range F → γ, ∀ a : α, Φ ⟨F a, ⟨a, rfl⟩⟩ = I a) ∧
      (∀ {U V : α}, F U = F V → I U = I V) := by
  classical
  let Φ : Set.range F → γ := fun y => I (Classical.choose y.2)
  refine ⟨?_, ?_⟩
  · refine ⟨Φ, ?_, ?_⟩
    · intro a
      have hchoose : F (Classical.choose (⟨F a, ⟨a, rfl⟩⟩ : Set.range F).2) = F a :=
        Classical.choose_spec (⟨F a, ⟨a, rfl⟩⟩ : Set.range F).2
      have hsame : Classical.choose (⟨F a, ⟨a, rfl⟩⟩ : Set.range F).2 = a := hF hchoose
      simp [Φ, hsame]
    · intro Ψ hΨ
      funext y
      rcases y with ⟨_, a, rfl⟩
      have hchoose : F (Classical.choose (⟨F a, ⟨a, rfl⟩⟩ : Set.range F).2) = F a :=
        Classical.choose_spec (⟨F a, ⟨a, rfl⟩⟩ : Set.range F).2
      have hsame : Classical.choose (⟨F a, ⟨a, rfl⟩⟩ : Set.range F).2 = a := hF hchoose
      simp [Φ, hsame, hΨ a]
  · intro U V hUV
    exact congrArg I (hF hUV)
