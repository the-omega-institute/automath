import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-foldbin-tail-spectrum-discrete-difference`. -/
theorem paper_xi_foldbin_tail_spectrum_discrete_difference (S : Nat -> Prop)
    [DecidablePred S] (d : Nat -> Nat)
    (hd : forall R, d R = Fintype.card {s : Fin (R + 1) // S s.1}) :
    forall R : Nat, d (R + 1) - d R = if S (R + 1) then 1 else 0 := by
  intro R
  classical
  have hcard : forall n : Nat, Fintype.card {s : Fin n // S s.1} = Nat.count S n := by
    intro n
    let _ : Fintype {k : Nat // k < n /\ S k} := Nat.CountSet.fintype S n
    let e : {s : Fin n // S s.1} ≃ {k : Nat // k < n /\ S k} :=
    {
      toFun s := ⟨s.1.1, s.1.2, s.2⟩
      invFun k := ⟨⟨k.1, k.2.1⟩, k.2.2⟩
      left_inv s := by
        ext
        rfl
      right_inv k := by
        ext
        rfl
    }
    exact (Fintype.card_congr e).trans (Nat.count_eq_card_fintype S n).symm
  rw [hd (R + 1), hd R, hcard (R + 2), hcard (R + 1)]
  rw [show R + 2 = (R + 1) + 1 by omega, Nat.count_succ]
  exact Nat.add_sub_cancel_left _ _

end Omega.Zeta
