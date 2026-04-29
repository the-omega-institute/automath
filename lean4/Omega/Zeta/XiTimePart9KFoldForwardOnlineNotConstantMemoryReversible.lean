import Mathlib.Data.Fintype.Prod

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9k-fold-forward-online-not-constant-memory-reversible`.
Correctly recovered states inject into the visible output and the `B` side-information bits. -/
theorem paper_xi_time_part9k_fold_forward_online_not_constant_memory_reversible
    {Omega X : Type*} [Fintype Omega] [Fintype X] [DecidableEq Omega] (B : Nat)
    (Fold : Omega -> X) (decode : X -> Fin (2 ^ B) -> Omega) (side : Omega -> Fin (2 ^ B)) :
    Fintype.card {w : Omega // decode (Fold w) (side w) = w} <=
      Fintype.card X * 2 ^ B := by
  let code : {w : Omega // decode (Fold w) (side w) = w} -> X × Fin (2 ^ B) :=
    fun w => (Fold w.1, side w.1)
  have hcode : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    have hfold : Fold a.1 = Fold b.1 := congrArg Prod.fst hab
    have hside : side a.1 = side b.1 := congrArg Prod.snd hab
    calc
      a.1 = decode (Fold a.1) (side a.1) := a.2.symm
      _ = decode (Fold b.1) (side b.1) := by rw [hfold, hside]
      _ = b.1 := b.2
  calc
    Fintype.card {w : Omega // decode (Fold w) (side w) = w} <=
        Fintype.card (X × Fin (2 ^ B)) :=
      Fintype.card_le_of_injective code hcode
    _ = Fintype.card X * 2 ^ B := by simp [Fintype.card_prod]

end Omega.Zeta
