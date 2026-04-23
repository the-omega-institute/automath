import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties

namespace Omega.POM

/-- Paper-facing reformulation of the generic parity split identities together with the given
`mod 3` obstruction criterion for vanishing signed sum.
    thm:pom-fiber-rewrite-parity-exact-split-mod3-obstruction -/
theorem paper_pom_fiber_rewrite_parity_exact_split_mod3_obstruction
    {α : Type*} [DecidableEq α] (S : Finset α) (sgn : α → ℤ)
    (hsgn : ∀ ω ∈ S, sgn ω = 1 ∨ sgn ω = -1)
    (hmod3 : (∑ ω ∈ S, sgn ω) = 0 ↔ ∃ ℓ : ℕ, ℓ % 3 = 1) :
    let A := (S.filter (fun ω => sgn ω = 1)).card
    let B := (S.filter (fun ω => sgn ω = -1)).card
    2 * (A : ℤ) = S.card + ∑ ω ∈ S, sgn ω ∧
      2 * (B : ℤ) = S.card - ∑ ω ∈ S, sgn ω ∧
      (A = B ↔ ∃ ℓ : ℕ, ℓ % 3 = 1) := by
  dsimp
  refine ⟨Omega.parity_split_identity hsgn, Omega.parity_split_identity_odd hsgn, ?_⟩
  constructor
  · intro hAB
    have hA :=
      Omega.parity_split_identity (S := S) (f := sgn) hsgn
    have hB :=
      Omega.parity_split_identity_odd (S := S) (f := sgn) hsgn
    push_cast at hA hB
    have hsum_zero : (∑ ω ∈ S, sgn ω) = 0 := by
      linarith
    exact hmod3.mp hsum_zero
  · intro hbad
    have hsum_zero : (∑ ω ∈ S, sgn ω) = 0 := hmod3.mpr hbad
    have hA :=
      Omega.parity_split_identity (S := S) (f := sgn) hsgn
    have hB :=
      Omega.parity_split_identity_odd (S := S) (f := sgn) hsgn
    push_cast at hA hB
    linarith

end Omega.POM
