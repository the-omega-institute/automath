import Mathlib.Tactic

namespace Omega.FoldComputability

/-- Concrete readout package for the three halting-equivalent observables.  Each observable is a
named predicate on the same code space, and the hypotheses assert that the three reductions all
recover the same halting predicate. -/
structure fold_computability_holography_torsion_fractal_halting_equivalent_data where
  Code : Type
  halts : Code → Prop
  holographyReadout : Code → Prop
  torsionReadout : Code → Prop
  fractalReadout : Code → Prop
  holography_halts_iff : ∀ c : Code, holographyReadout c ↔ halts c
  torsion_halts_iff : ∀ c : Code, torsionReadout c ↔ halts c
  fractal_halts_iff : ∀ c : Code, fractalReadout c ↔ halts c

namespace fold_computability_holography_torsion_fractal_halting_equivalent_data

/-- The holographic spectrum readout decides halting. -/
def fold_computability_holography_torsion_fractal_halting_equivalent_holography_equiv
    (D : fold_computability_holography_torsion_fractal_halting_equivalent_data) : Prop :=
  ∀ c : D.Code, D.holographyReadout c ↔ D.halts c

/-- The torsion-tower readout decides halting. -/
def fold_computability_holography_torsion_fractal_halting_equivalent_torsion_equiv
    (D : fold_computability_holography_torsion_fractal_halting_equivalent_data) : Prop :=
  ∀ c : D.Code, D.torsionReadout c ↔ D.halts c

/-- The fractal-dimension readout decides halting. -/
def fold_computability_holography_torsion_fractal_halting_equivalent_fractal_equiv
    (D : fold_computability_holography_torsion_fractal_halting_equivalent_data) : Prop :=
  ∀ c : D.Code, D.fractalReadout c ↔ D.halts c

end fold_computability_holography_torsion_fractal_halting_equivalent_data

open fold_computability_holography_torsion_fractal_halting_equivalent_data

/-- Paper label: `cor:fold-computability-holography-torsion-fractal-halting-equivalent`. The
holographic spectrum, torsion-tower deviation depth, and fractal-dimension readouts are all
Turing-equivalent because each one recovers the same halting predicate on the code space. -/
theorem paper_fold_computability_holography_torsion_fractal_halting_equivalent
    (D : fold_computability_holography_torsion_fractal_halting_equivalent_data) :
    D.fold_computability_holography_torsion_fractal_halting_equivalent_holography_equiv ∧
      D.fold_computability_holography_torsion_fractal_halting_equivalent_torsion_equiv ∧
      D.fold_computability_holography_torsion_fractal_halting_equivalent_fractal_equiv := by
  exact ⟨D.holography_halts_iff, D.torsion_halts_iff, D.fractal_halts_iff⟩

end Omega.FoldComputability
