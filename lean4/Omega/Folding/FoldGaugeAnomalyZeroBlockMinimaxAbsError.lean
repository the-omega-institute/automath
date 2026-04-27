import Mathlib.Tactic

theorem paper_fold_gauge_anomaly_zero_block_minimax_abs_error
    (E : Nat -> Rat) (F : Nat -> Nat) (alpha : Nat -> Rat) (n : Nat) (hn : 2 <= n)
    (h_minimax :
      E n = (1 / 2) * max (alpha (n - 1) - alpha n) (alpha n - alpha (n - 1)))
    (h_alpha :
      max (alpha (n - 1) - alpha n) (alpha n - alpha (n - 1)) =
        (1 : Rat) / (2 * (F (n + 3) : Rat) * (F (n + 4) : Rat))) :
    E n = (1 : Rat) / (4 * (F (n + 3) : Rat) * (F (n + 4) : Rat)) := by
  have _ : 2 <= n := hn
  rw [h_minimax, h_alpha]
  ring_nf
