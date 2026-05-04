import Mathlib.GroupTheory.Perm.Fin
import Omega.CircleDimension.CdimResolventCubicBranchpointsAndComplementaryRamification

namespace Omega.CircleDimension

/-- Concrete marker for the six-branch transposition package. -/
abbrev cdim_s4_v4_six_branch_transposition_data := Unit

/-- The six branch values inherited from the resolvent-cubic package. -/
def cdim_s4_v4_six_branch_transposition_branch_values : Finset (Fin 6) :=
  cdim_resolvent_cubic_branchpoints_and_complementary_ramification_branch_values

/-- The three ramified points over each branch value in the `S₃` cover. -/
def cdim_s4_v4_six_branch_transposition_ramified_points :
    Finset (Fin 6 × Fin 3) :=
  Finset.univ

/-- The fiber of ramified points over one branch value. -/
def cdim_s4_v4_six_branch_transposition_ramified_fiber
    (i : Fin 6) : Finset (Fin 6 × Fin 3) :=
  cdim_s4_v4_six_branch_transposition_ramified_points.filter fun p => p.1 = i

/-- Local inertia at every branch value: a fixed transposition in the `S₃` fiber. -/
def cdim_s4_v4_six_branch_transposition_inertia (_i : Fin 6) :
    Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

/-- Concrete transposition certificate on the three-point fiber. -/
def cdim_s4_v4_six_branch_transposition_is_transposition
    (σ : Equiv.Perm (Fin 3)) : Prop :=
  σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2

/-- Degree of the `S₃` cover. -/
def cdim_s4_v4_six_branch_transposition_degree : ℤ :=
  6

/-- Ramification index at each marked point. -/
def cdim_s4_v4_six_branch_transposition_ramification_index
    (_p : Fin 6 × Fin 3) : ℕ :=
  2

/-- Genus obtained from the recorded Riemann-Hurwitz count. -/
def cdim_s4_v4_six_branch_transposition_genus : ℤ :=
  4

/-- Riemann-Hurwitz left-hand side for the `S₃` cover. -/
def cdim_s4_v4_six_branch_transposition_riemann_hurwitz_lhs : ℤ :=
  2 * cdim_s4_v4_six_branch_transposition_genus - 2

/-- Riemann-Hurwitz right-hand side for degree six over genus zero with eighteen simple
ramification points. -/
def cdim_s4_v4_six_branch_transposition_riemann_hurwitz_rhs : ℤ :=
  cdim_s4_v4_six_branch_transposition_degree * (2 * 0 - 2) +
    (cdim_s4_v4_six_branch_transposition_ramified_points.card : ℤ) * (2 - 1)

lemma cdim_s4_v4_six_branch_transposition_ramified_fiber_card (i : Fin 6) :
    (cdim_s4_v4_six_branch_transposition_ramified_fiber i).card = 3 := by
  fin_cases i <;> native_decide

lemma cdim_s4_v4_six_branch_transposition_inertia_pattern (i : Fin 6) :
    cdim_s4_v4_six_branch_transposition_is_transposition
      (cdim_s4_v4_six_branch_transposition_inertia i) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rfl

namespace cdim_s4_v4_six_branch_transposition_data

/-- Paper-facing statement: the resolvent package supplies the six branch values and `(2,1)`
fibers; the `S₃` cover has three simply ramified points over each branch value, transposition
inertia, and the Riemann-Hurwitz count gives genus four. -/
def statement (_D : cdim_s4_v4_six_branch_transposition_data) : Prop :=
  let R : cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data := ⟨()⟩
  R.statement ∧
    cdim_s4_v4_six_branch_transposition_branch_values.card = 6 ∧
    (∀ i : Fin 6,
      (cdim_s4_v4_six_branch_transposition_ramified_fiber i).card = 3) ∧
    (∀ i : Fin 6,
      cdim_s4_v4_six_branch_transposition_is_transposition
        (cdim_s4_v4_six_branch_transposition_inertia i)) ∧
    (∀ p : Fin 6 × Fin 3,
      cdim_s4_v4_six_branch_transposition_ramification_index p = 2) ∧
    cdim_s4_v4_six_branch_transposition_ramified_points.card = 18 ∧
    cdim_s4_v4_six_branch_transposition_degree = 6 ∧
    cdim_s4_v4_six_branch_transposition_riemann_hurwitz_lhs =
      cdim_s4_v4_six_branch_transposition_riemann_hurwitz_rhs ∧
    cdim_s4_v4_six_branch_transposition_genus = 4

end cdim_s4_v4_six_branch_transposition_data

open cdim_s4_v4_six_branch_transposition_data

/-- Paper label: `con:cdim-s4-v4-six-branch-transposition`. -/
theorem paper_cdim_s4_v4_six_branch_transposition
    (D : cdim_s4_v4_six_branch_transposition_data) : D.statement := by
  let R : cdim_resolvent_cubic_branchpoints_and_complementary_ramification_data := ⟨()⟩
  have hR : R.statement :=
    paper_cdim_resolvent_cubic_branchpoints_and_complementary_ramification R
  dsimp [cdim_s4_v4_six_branch_transposition_data.statement, R]
  refine ⟨hR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [cdim_s4_v4_six_branch_transposition_branch_values] using hR.1
  · intro i
    exact cdim_s4_v4_six_branch_transposition_ramified_fiber_card i
  · intro i
    exact cdim_s4_v4_six_branch_transposition_inertia_pattern i
  · intro p
    rfl
  · decide
  · rfl
  · norm_num [cdim_s4_v4_six_branch_transposition_riemann_hurwitz_lhs,
      cdim_s4_v4_six_branch_transposition_riemann_hurwitz_rhs,
      cdim_s4_v4_six_branch_transposition_genus,
      cdim_s4_v4_six_branch_transposition_degree,
      cdim_s4_v4_six_branch_transposition_ramified_points]

end Omega.CircleDimension
