import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Finite-surjection seed data for the Beck--Chevalley Radon--Nikodym curvature identity. The
source weight is transported to the target point `x`, while the two fiber-cardinality functions
record the sequential and direct lift multiplicities above `x`. -/
structure pom_bc_radon_nikodym_curvature_data where
  X : Type
  sourceWeight : X → ℝ
  sourceWeight_pos : ∀ x, 0 < sourceWeight x
  sequentialFiberCard : X → ℕ
  sequentialFiberCard_pos : ∀ x, 0 < sequentialFiberCard x
  directFiberCard : X → ℕ
  directFiberCard_pos : ∀ x, 0 < directFiberCard x

namespace pom_bc_radon_nikodym_curvature_data

/-- Sequential lift probability at `x`: source weight divided by the sequential fiber size. -/
def sequential (D : pom_bc_radon_nikodym_curvature_data) (x : D.X) : ℝ :=
  D.sourceWeight x / D.sequentialFiberCard x

/-- Direct lift probability at `x`: source weight divided by the direct fiber size. -/
def direct (D : pom_bc_radon_nikodym_curvature_data) (x : D.X) : ℝ :=
  D.sourceWeight x / D.directFiberCard x

/-- Curvature term coming from the logarithmic ratio of the two fiber cardinalities. -/
def curvature (D : pom_bc_radon_nikodym_curvature_data) (x : D.X) : ℝ :=
  Real.log ((D.directFiberCard x : ℝ) / D.sequentialFiberCard x)

end pom_bc_radon_nikodym_curvature_data

/-- Paper label: `prop:pom-bc-radon-nikodym-curvature`. For the concrete finite-surjection model,
the sequential-to-direct Radon--Nikodym logarithmic ratio is exactly the curvature term coming
from the fiber-cardinality defect. -/
theorem paper_pom_bc_radon_nikodym_curvature (D : pom_bc_radon_nikodym_curvature_data) :
    forall x, Real.log (D.sequential x / D.direct x) = D.curvature x := by
  intro x
  have hsource_ne : D.sourceWeight x ≠ 0 := ne_of_gt (D.sourceWeight_pos x)
  have hseq_ne : (D.sequentialFiberCard x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.sequentialFiberCard_pos x)
  have hdir_ne : (D.directFiberCard x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.directFiberCard_pos x)
  have hratio :
      D.sequential x / D.direct x =
        (D.directFiberCard x : ℝ) / D.sequentialFiberCard x := by
    unfold pom_bc_radon_nikodym_curvature_data.sequential
      pom_bc_radon_nikodym_curvature_data.direct
    field_simp [hsource_ne, hseq_ne, hdir_ne]
  rw [hratio]
  rfl

end

end Omega.POM
