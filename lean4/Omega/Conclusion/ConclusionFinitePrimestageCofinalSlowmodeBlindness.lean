import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-primestage-cofinal-slowmode-blindness`. -/
theorem paper_conclusion_finite_primestage_cofinal_slowmode_blindness
    (PrimeInStage NearUnit VisibleKernelMissing : Nat -> Prop)
    (hNear : forall eps : Nat, 0 < eps -> exists p, NearUnit p /\ Not (PrimeInStage p))
    (hBlind : forall p, Not (PrimeInStage p) -> VisibleKernelMissing p) :
    forall eps : Nat, 0 < eps -> exists p, NearUnit p /\ Not (PrimeInStage p) /\
      VisibleKernelMissing p := by
  intro eps heps
  rcases hNear eps heps with ⟨p, hpNear, hpOutside⟩
  exact ⟨p, hpNear, hpOutside, hBlind p hpOutside⟩

end Omega.Conclusion
