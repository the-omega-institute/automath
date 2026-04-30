import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-history-recovery-radial-profinite-double-completeness`.
Branch-coded compatible inverse-limit chains with the same root and successor branch codes are
equal. -/
theorem paper_conclusion_history_recovery_radial_profinite_double_completeness {X Code : Type*}
    (T : X → X) (beta : X → Code) (decode : X → Code → X)
    (hdecode : ∀ x c y, T y = x → beta y = c → decode x c = y) (x y : Nat → X)
    (hx : ∀ n, T (x (n + 1)) = x n) (hy : ∀ n, T (y (n + 1)) = y n)
    (h0 : x 0 = y 0) (hcode : ∀ n, beta (x (n + 1)) = beta (y (n + 1))) :
    x = y := by
  funext n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      have hxdec : decode (x n) (beta (x (n + 1))) = x (n + 1) :=
        hdecode (x n) (beta (x (n + 1))) (x (n + 1)) (hx n) rfl
      have hydec : decode (y n) (beta (y (n + 1))) = y (n + 1) :=
        hdecode (y n) (beta (y (n + 1))) (y (n + 1)) (hy n) rfl
      calc
        x (n + 1) = decode (x n) (beta (x (n + 1))) := hxdec.symm
        _ = decode (y n) (beta (y (n + 1))) := by rw [ih, hcode n]
        _ = y (n + 1) := hydec

end Omega.Conclusion
