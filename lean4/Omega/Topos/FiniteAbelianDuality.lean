import Mathlib.Data.Set.Basic

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the finite-abelian-duality lemma in the
    gluing-failure paper.
    lem:finite-abelian-duality -/
theorem paper_gluing_failure_finite_abelian_duality
    {A T : Type*} [One T]
    (H : Set A) (characters : Set (A → T))
    (hforward :
      ∀ ⦃a : A⦄, a ∈ H → ∀ ⦃χ : A → T⦄, χ ∈ characters → χ a = 1)
    (hbackward : ∀ ⦃a : A⦄, a ∉ H → ∃ χ ∈ characters, χ a ≠ 1) :
    H = {a : A | ∀ ⦃χ : A → T⦄, χ ∈ characters → χ a = 1} := by
  ext a
  constructor
  · intro ha χ hχ
    exact hforward ha hχ
  · intro ha
    by_contra hnot
    rcases hbackward hnot with ⟨χ, hχ, hχa⟩
    exact hχa (ha hχ)

end Omega.Topos
