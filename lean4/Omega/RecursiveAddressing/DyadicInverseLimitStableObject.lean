import Mathlib.Data.Set.Basic

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the standard inverse-limit facts used in the
    recursive-addressing dyadic tower.
    thm:recursive-addressing-dyadic-inverse-limit-stable-object -/
theorem paper_recursive_addressing_dyadic_inverse_limit_stable_object
    {Ainf Y : Type*}
    (dyadicCompact dyadicComplete dyadicTotallyDisconnected dyadicUltrametric : Prop)
    (stableFiber : Ainf → Set Y)
    (hnonempty : Nonempty Ainf)
    (hstructure :
      dyadicCompact ∧ dyadicComplete ∧ dyadicTotallyDisconnected ∧ dyadicUltrametric)
    (hstable : ∀ a, ∃! y, y ∈ stableFiber a) :
    Nonempty Ainf ∧
      dyadicCompact ∧
      dyadicComplete ∧
      dyadicTotallyDisconnected ∧
      dyadicUltrametric ∧
      ∀ a, ∃! y, y ∈ stableFiber a := by
  rcases hstructure with ⟨hCompact, hComplete, hTotDisc, hUltra⟩
  exact ⟨hnonempty, hCompact, hComplete, hTotDisc, hUltra, hstable⟩

end Omega.RecursiveAddressing
