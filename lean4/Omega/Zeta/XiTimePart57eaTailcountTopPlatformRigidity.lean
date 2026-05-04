import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part57ea-tailcount-top-platform-rigidity`. -/
theorem paper_xi_time_part57ea_tailcount_top_platform_rigidity {X : Type*} [Fintype X]
    [DecidableEq X] (d : X → ℕ) (M T K : ℕ) (Amax : Finset X)
    (hAmax : ∀ x, x ∈ Amax ↔ d x = M) (hTop : ∀ x, x ∈ Amax → T ≤ d x)
    (hOutside : ∀ x, x ∉ Amax → d x < T) (hK : Amax.card = K) :
    (Finset.univ.filter (fun x => T ≤ d x)).card = K := by
  have _ : ∀ x, x ∈ Amax ↔ d x = M := hAmax
  have hTail : Finset.univ.filter (fun x => T ≤ d x) = Amax := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      by_contra hxA
      exact (Nat.not_lt_of_ge hx) (hOutside x hxA)
    · intro hxA
      exact hTop x hxA
  rw [hTail, hK]

end Omega.Zeta
