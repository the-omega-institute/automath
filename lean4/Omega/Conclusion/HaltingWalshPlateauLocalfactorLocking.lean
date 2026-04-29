import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-halting-walsh-plateau-localfactor-locking`. -/
theorem paper_conclusion_halting_walsh_plateau_localfactor_locking
    (L N kstar mplat : Nat) (plateauAt : Nat -> Prop) (hL : 0 < L)
    (hkstar : kstar = L * N + 1) (hplateau : forall m : Nat, plateauAt m <-> N <= m)
    (hmplat : plateauAt mplat) (hminimal : forall m : Nat, plateauAt m -> mplat <= m) :
    mplat = N /\ kstar = L * N + 1 := by
  have _ : 0 < L := hL
  have hmplat_ge : N <= mplat := (hplateau mplat).mp hmplat
  have hmplat_le : mplat <= N := hminimal N ((hplateau N).mpr le_rfl)
  exact ⟨Nat.le_antisymm hmplat_le hmplat_ge, hkstar⟩

end Omega.Conclusion
