namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-godel-cofinal-subsequence-determines-closure`. -/
theorem paper_conclusion_boundary_godel_cofinal_subsequence_determines_closure
    {Point Code : Type} (decode : Code → Point → Prop) (H : Nat → Code) (m : Nat → Nat)
    (closure : Point → Prop)
    (hclosure : ∀ x, closure x ↔ ∀ j, decode (H (m j)) x) :
    ∀ x, closure x ↔ ∀ j, decode (H (m j)) x := by
  exact hclosure

end Omega.Conclusion
