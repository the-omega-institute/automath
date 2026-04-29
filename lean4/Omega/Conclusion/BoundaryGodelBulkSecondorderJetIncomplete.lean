import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-godel-bulk-secondorder-jet-incomplete`. -/
theorem paper_conclusion_boundary_godel_bulk_secondorder_jet_incomplete
    {Obj : Type}
    (dG dBoundary gamma content : Obj → ℝ)
    (A B : Obj)
    (d n M : ℝ)
    (hA : dG A = d)
    (hB : dG B = d)
    (hdlt : d < n)
    (hMA : content A = M)
    (hMB : content B = M)
    (hphase : ∀ X, dG X < n → dBoundary X = gamma X)
    (hgamma : gamma A ≠ gamma B) :
    dBoundary A ≠ dBoundary B := by
  have _ : content A = M := hMA
  have _ : content B = M := hMB
  intro hboundary
  apply hgamma
  calc
    gamma A = dBoundary A := (hphase A (by simpa [hA] using hdlt)).symm
    _ = dBoundary B := hboundary
    _ = gamma B := hphase B (by simpa [hB] using hdlt)

end Omega.Conclusion
