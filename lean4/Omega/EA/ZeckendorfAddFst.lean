import Omega.EA.AddAsFold

namespace Omega.EA

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for Zeckendorf addition as normalization of the
    digitwise overlay.
    thm:zeckendorf-add-fst -/
theorem paper_zeckendorf_add_fst {m : ℕ} (c d : Omega.Word m) :
    Omega.X.stableAdd (Omega.Fold c) (Omega.Fold d) =
      Omega.X.ofNat m ((Omega.weight c + Omega.weight d) % Nat.fib (m + 2)) :=
  paper_ea_add_as_fold_seeds c d

end Omega.EA
