import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-ranktwo-smith-audit-constant-on-boolean-torsor`. A Boolean
torsor with a constant Smith pair has all audit channels constant, pointwise, because each
channel depends only on that Smith pair. -/
theorem paper_conclusion_ranktwo_smith_audit_constant_on_boolean_torsor
    (C : Type) (smith : C -> Nat × Nat) (audit : C -> Nat -> Nat)
    (localZeta : C -> Nat -> Nat -> Nat) (mobiusAtom : C -> Nat -> Nat -> Int)
    (minScale maxScale : C -> Nat -> Prop)
    (hsmith : forall c d : C, smith c = smith d)
    (haudit : forall c d m, smith c = smith d -> audit c m = audit d m)
    (hzeta : forall c d p k, smith c = smith d -> localZeta c p k = localZeta d p k)
    (hmobius : forall c d p k, smith c = smith d -> mobiusAtom c p k = mobiusAtom d p k)
    (hmin : forall c d m, smith c = smith d -> (minScale c m <-> minScale d m))
    (hmax : forall c d m, smith c = smith d -> (maxScale c m <-> maxScale d m)) :
    (forall c d m, audit c m = audit d m) ∧
      (forall c d p k, localZeta c p k = localZeta d p k) ∧
        (forall c d p k, mobiusAtom c p k = mobiusAtom d p k) ∧
          (forall c d m, minScale c m <-> minScale d m) ∧
            (forall c d m, maxScale c m <-> maxScale d m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c d m
    exact haudit c d m (hsmith c d)
  · intro c d p k
    exact hzeta c d p k (hsmith c d)
  · intro c d p k
    exact hmobius c d p k (hsmith c d)
  · intro c d m
    exact hmin c d m (hsmith c d)
  · intro c d m
    exact hmax c d m (hsmith c d)

end Omega.Conclusion
