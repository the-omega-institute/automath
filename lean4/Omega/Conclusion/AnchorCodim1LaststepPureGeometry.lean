import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-anchor-codim1-laststep-pure-geometry`. -/
theorem paper_conclusion_anchor_codim1_laststep_pure_geometry {Point : Type} (cA : Real)
    (hcA : 0 < cA) (ratio potential : Point -> Real)
    (hformula : forall x, ratio x = cA * potential x) :
    (forall x, ratio x = cA * potential x) ∧
      (forall x,
        (forall y, ratio y <= ratio x) <-> (forall y, potential y <= potential x)) := by
  refine ⟨hformula, ?_⟩
  intro x
  constructor
  · intro hmax y
    have hscaled : cA * potential y <= cA * potential x := by
      simpa [hformula y, hformula x] using hmax y
    nlinarith [hcA, hscaled]
  · intro hmax y
    have hscaled : cA * potential y <= cA * potential x :=
      mul_le_mul_of_nonneg_left (hmax y) (le_of_lt hcA)
    simpa [hformula y, hformula x] using hscaled

end Omega.Conclusion
