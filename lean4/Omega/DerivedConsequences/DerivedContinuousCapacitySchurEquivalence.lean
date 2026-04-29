import Mathlib.Data.Fintype.Card
import Omega.Conclusion.CapacityFiniteCompleteness
import Omega.POM.InvertWFromHomogeneousCurve
import Omega.Zeta.XiTimePart63cSchurCauchyMasterKernel

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- Paper label: `thm:derived-continuous-capacity-schur-equivalence`. For any finite multiplicity
profile, the continuous capacity curve determines the histogram/tail/moment data, while the Schur
generating series externalizes through the one-variable complete-homogeneous kernels and the
homogeneous curve determines the elementary coefficients on every finite prefix. -/
def paper_derived_continuous_capacity_schur_equivalence : Prop := by
  exact
    ∀ {X : Type} [Fintype X] [DecidableEq X] (d : X → ℕ),
      let h : ℕ → ℕ := fun t => Fintype.card {x : X // d x = t}
      let N : ℕ → ℕ := fun t => Fintype.card {x : X // t ≤ d x}
      let C : ℕ → ℕ := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d t
      let S : ℕ → ℕ := fun q => ∑ x : X, d x ^ q
      Omega.Conclusion.FiniteMultiplicityDataEquivalent (X := X) h N C S ∧
        (∀ {β : Type} [Fintype β] (y : β → ℚ),
          Omega.Zeta.xiSchurTraceSeries (fun x => (d x : ℚ)) y =
            Omega.Zeta.xiSchurCauchyMasterKernel (fun x => (d x : ℚ)) y ∧
            Omega.Zeta.xiSchurCauchyMasterKernel (fun x => (d x : ℚ)) y =
              ∏ j, Omega.Zeta.xiHmKernel (fun x => (d x : ℚ)) (y j)) ∧
        (∀ (n : ℕ) (hSeq e e' : ℕ → ℚ), hSeq 0 = 1 → e 0 = 1 → e' 0 = 1 →
          (∀ t < n, hSeq (t + 1) = Omega.POM.completeHomogeneousRecurrence e hSeq t) →
          (∀ t < n, hSeq (t + 1) = Omega.POM.completeHomogeneousRecurrence e' hSeq t) →
          ∀ t ≤ n, e t = e' t)

end Omega.DerivedConsequences
