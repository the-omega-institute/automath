import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-saturated-observer-closure`. -/
theorem paper_conclusion_fibadic_saturated_observer_closure
    {Depth Conductor Observer Newspace Packet Algebra : Type} (active : Depth → Prop)
    (conductorOf : Depth → Conductor) (observerOf : Conductor → Observer)
    (newspaceOf : Depth → Newspace) (packetOf : Depth → Packet) (algebraOf : Nat → Algebra)
    (conductorLocked : Depth → Conductor → Prop)
    (observerLocked : Conductor → Observer → Prop)
    (newspaceEquivalent : Observer → Newspace → Prop) (packetMinimal : Newspace → Packet → Prop)
    (algebraControlled : Observer → Packet → Algebra → Prop)
    (h1 : ∀ d, active d → conductorLocked d (conductorOf d))
    (h2 : ∀ d, active d → observerLocked (conductorOf d) (observerOf (conductorOf d)))
    (h3 : ∀ d, active d → newspaceEquivalent (observerOf (conductorOf d)) (newspaceOf d))
    (h4 : ∀ d, active d → packetMinimal (newspaceOf d) (packetOf d))
    (h5 : ∀ d N, active d →
      algebraControlled (observerOf (conductorOf d)) (packetOf d) (algebraOf N))
    (d : Depth) (N : Nat) :
    active d →
      ∃ F G X P A,
        conductorLocked d F ∧
          observerLocked F G ∧
            newspaceEquivalent G X ∧ packetMinimal X P ∧ algebraControlled G P A := by
  intro hd
  exact ⟨conductorOf d, observerOf (conductorOf d), newspaceOf d, packetOf d, algebraOf N,
    h1 d hd, h2 d hd, h3 d hd, h4 d hd, h5 d N hd⟩

end Omega.Conclusion
