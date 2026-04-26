import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FiberMultiplicityDiameterCubedimRigidity
import Omega.Conclusion.LucasPowerHankelClosedForm

open scoped goldenRatio

namespace Omega.Conclusion

/-- The weighted Fibonacci list underlying the Hankel closed form: the entry `d - 1` appears with
multiplicity `2 * (q - d)`, matching the factor `F_d^(2(q-d))`. -/
def conclusion_golden_lucas_hankel_archimedean_cubic_growth_lengths (q : ℕ) : List ℕ :=
  ((List.range q).map fun d => List.replicate (2 * (q - d)) (d - 1)).flatten

/-- Paper label: `thm:conclusion-golden-lucas-hankel-archimedean-cubic-growth`.
The golden-ratio Lucas Hankel determinant has the existing closed form, and its weighted Fibonacci
factor is exactly the multiplicity product associated to the explicit length list above. The public
golden-ratio product bounds therefore isolate the source of the eventual cubic archimedean growth:
the Fibonacci factor is sandwiched between the diameter-scale lower bound and the
diameter-plus-length upper bound. -/
theorem paper_conclusion_golden_lucas_hankel_archimedean_cubic_growth (q : ℕ) :
    lucasPowerHankelDet q =
      (∏ k ∈ Finset.range (q + 1), Nat.choose q k) *
        5 ^ (q * (q + 1) / 2) *
        (∏ d ∈ Finset.range q, Nat.fib (d + 1) ^ (2 * (q - d))) ∧
      let lengths := conclusion_golden_lucas_hankel_archimedean_cubic_growth_lengths q
      Real.goldenRatio ^ Omega.POM.fiberReconstructionDiameter lengths ≤
          conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ∧
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ≤
          Real.goldenRatio ^
            (Omega.POM.fiberReconstructionDiameter lengths + lengths.length) := by
  refine ⟨paper_conclusion_lucas_power_hankel_closed_form q, ?_⟩
  dsimp [conclusion_golden_lucas_hankel_archimedean_cubic_growth_lengths]
  let h :=
    paper_conclusion_fiber_multiplicity_diameter_cubedim_rigidity
      (((List.range q).map fun d => List.replicate (2 * (q - d)) (d - 1)).flatten)
  exact ⟨h.1, h.2.1⟩

end Omega.Conclusion
