import Mathlib.Tactic

namespace Omega.Conclusion

/-- Transporting a nonzero obstruction class along observer renaming produces an obstruction, and
the obstruction-to-null interface then supplies a null-fiber address for every observer.
    thm:conclusion-observer-cech-null-propagation -/
theorem paper_conclusion_observer_cech_null_propagation {Observer Address : Type*}
    (rename : Observer → Observer → Address → Address)
    (obstruction nullFiber : Observer → Address → Prop)
    (transport : ∀ i j a, obstruction i a → obstruction j (rename i j a))
    (toNull : ∀ i a, obstruction i a → nullFiber i a)
    {i0 : Observer} {a0 : Address} (h0 : obstruction i0 a0) :
    ∀ j : Observer, ∃ a : Address, obstruction j a ∧ nullFiber j a := by
  intro j
  let a := rename i0 j a0
  have ha : obstruction j a := transport i0 j a0 h0
  exact ⟨a, ha, toNull j a ha⟩

end Omega.Conclusion
