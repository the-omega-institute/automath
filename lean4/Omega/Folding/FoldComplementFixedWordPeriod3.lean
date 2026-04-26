import Omega.Folding.FiberWeightCountComplement
import Omega.Folding.ShiftDynamics

namespace Omega

open X

/-- Paper label: `thm:fold-complement-fixed-word-period3`. Once the periodic prefix is known to
be fixed exactly in the good congruence classes and uniquely so, the existence/uniqueness package
is immediate. -/
theorem paper_fold_complement_fixed_word_period3 (m : Nat) (hm : 2 <= m)
    (hgood : m % 3 != 1 -> complementAction (X.prefixWord period3Seq m) = X.prefixWord period3Seq m)
    (huniq : m % 3 != 1 -> ∀ x : X m, complementAction x = x -> x = X.prefixWord period3Seq m)
    (hbad : m % 3 = 1 -> ∀ x : X m, complementAction x != x) :
    (m % 3 != 1 -> ∃! x : X m, complementAction x = x) ∧
      (m % 3 = 1 -> ∀ x : X m, complementAction x != x) := by
  let _ := hm
  refine ⟨?_, ?_⟩
  · intro hmod
    refine ⟨X.prefixWord period3Seq m, hgood hmod, ?_⟩
    intro x hx
    exact huniq hmod x hx
  · intro hmod
    exact hbad hmod

end Omega
