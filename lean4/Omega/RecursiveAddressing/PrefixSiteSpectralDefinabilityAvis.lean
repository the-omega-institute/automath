import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- Paper-facing factorization criterion for
`thm:prefix-site-spectral-definability-avis`.

A spectral observable on the full addressing space descends to the visible quotient exactly when
it is constant on the fibers of the quotient map. The `Nonempty Spec` hypothesis handles the
off-image branch when `pi` is not surjective. -/
theorem paper_recursive_addressing_prefix_site_spectral_definability_avis
    {A Avis Spec : Type*} [Nonempty Spec] (pi : A → Avis) (q : A → Spec) :
    (∃ qvis : Avis → Spec, q = fun a => qvis (pi a)) ↔
      ∀ a1 a2, pi a1 = pi a2 → q a1 = q a2 := by
  classical
  constructor
  · rintro ⟨qvis, hq⟩ a1 a2 hpi
    simp [hq, hpi]
  · intro hfiber
    let qvis : Avis → Spec := fun avis =>
      if hvis : ∃ a, pi a = avis then q (Classical.choose hvis) else Classical.choice inferInstance
    refine ⟨qvis, funext ?_⟩
    intro a
    have hvis : ∃ a', pi a' = pi a := ⟨a, rfl⟩
    rw [show qvis (pi a) = q (Classical.choose hvis) by simp [qvis, hvis]]
    exact hfiber a (Classical.choose hvis) (Classical.choose_spec hvis).symm

end Omega.RecursiveAddressing
