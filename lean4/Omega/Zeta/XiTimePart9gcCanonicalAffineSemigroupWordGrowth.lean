import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9gc-canonical-affine-semigroup-word-growth`. -/
theorem paper_xi_time_part9gc_canonical_affine_semigroup_word_growth {α : Type}
    [DecidableEq α] (M k : Nat) (wordValue : (Fin k -> Fin (M + 1)) -> α)
    (hfaithful : Function.Injective wordValue) :
    (Finset.univ.image wordValue).card = (M + 1) ^ k := by
  classical
  rw [Finset.card_image_of_injective _]
  · calc
      (Finset.univ : Finset (Fin k -> Fin (M + 1))).card =
          Fintype.card (Fin k -> Fin (M + 1)) := by
        simp
      _ = Fintype.card (Fin (M + 1)) ^ Fintype.card (Fin k) :=
        Fintype.card_fun
      _ = (M + 1) ^ k := by
        simp
  · exact hfaithful

end Omega.Zeta
