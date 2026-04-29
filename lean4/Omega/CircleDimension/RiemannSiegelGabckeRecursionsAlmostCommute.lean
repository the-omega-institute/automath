import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.RiemannSiegelGabckeLocalZeroStability

namespace Omega.CircleDimension

/-- Concrete local refinement data for one Gabcke truncation step. The two remainder levels
`eK, eK1` share the same affine zero model, and `deltaSup` controls the local size of the
inter-level difference. -/
structure RiemannSiegelGabckeLocalRefinement where
  γ : ℝ
  ρ : ℝ
  m : ℝ
  eK : ℝ
  eK1 : ℝ
  deltaSup : ℝ
  hρ : 0 < ρ
  hm : 0 < m
  heK : |eK| ≤ m * ρ
  heK1 : |eK1| ≤ m * ρ
  hdelta : |eK1 - eK| ≤ 2 * deltaSup

namespace RiemannSiegelGabckeLocalRefinement

/-- The certified `K`-level approximate zero. -/
noncomputable def approxZeroK (D : RiemannSiegelGabckeLocalRefinement) : ℝ :=
  rsGabckeApproxZero D.γ D.m D.eK

/-- The certified `(K+1)`-level approximate zero. -/
noncomputable def approxZeroK1 (D : RiemannSiegelGabckeLocalRefinement) : ℝ :=
  rsGabckeApproxZero D.γ D.m D.eK1

/-- The local refinement displacement from order `K` to order `K+1`. -/
noncomputable def refinementStep (D : RiemannSiegelGabckeLocalRefinement) : ℝ :=
  D.approxZeroK1 - D.approxZeroK

lemma refinementStep_bound_raw (D : RiemannSiegelGabckeLocalRefinement) :
    |D.refinementStep| ≤ |D.eK1 - D.eK| / D.m := by
  have h :=
    paper_cdim_rs_gabcke_local_zero_stability D.γ D.ρ D.m D.eK D.eK1
      D.hρ D.hm D.heK D.heK1
  dsimp [refinementStep, approxZeroK, approxZeroK1] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hstep⟩
  simpa using hstep

lemma refinementStep_bound (D : RiemannSiegelGabckeLocalRefinement) :
    |D.refinementStep| ≤ (2 * D.deltaSup) / D.m := by
  have hm : 0 ≤ D.m := le_of_lt D.hm
  have hdiv : |D.eK1 - D.eK| / D.m ≤ (2 * D.deltaSup) / D.m :=
    div_le_div_of_nonneg_right D.hdelta hm
  exact le_trans D.refinementStep_bound_raw hdiv

end RiemannSiegelGabckeLocalRefinement

open RiemannSiegelGabckeLocalRefinement

/-- Two neighboring zero certificates, one for `n` and one for `n+1`, together with their
respective refinement-step bounds. -/
structure RiemannSiegelGabckeRecursionData where
  current : RiemannSiegelGabckeLocalRefinement
  next : RiemannSiegelGabckeLocalRefinement

namespace RiemannSiegelGabckeRecursionData

/-- The `K`-level zero after advancing the zero index. -/
noncomputable def advanceAtK (D : RiemannSiegelGabckeRecursionData) : ℝ :=
  D.next.approxZeroK

/-- The `(K+1)`-level zero after advancing the zero index. -/
noncomputable def advanceAtK1 (D : RiemannSiegelGabckeRecursionData) : ℝ :=
  D.next.approxZeroK1

/-- The `(K+1)`-level zero before advancing the zero index. -/
noncomputable def refineAtCurrent (D : RiemannSiegelGabckeRecursionData) : ℝ :=
  D.current.approxZeroK1

/-- The starting `K`-level zero. -/
noncomputable def baseAtCurrent (D : RiemannSiegelGabckeRecursionData) : ℝ :=
  D.current.approxZeroK

/-- The commutator between index advance and refinement, written as the difference of the two
local refinement steps. -/
noncomputable def commutator (D : RiemannSiegelGabckeRecursionData) : ℝ :=
  (D.advanceAtK1 - D.advanceAtK) - (D.refineAtCurrent - D.baseAtCurrent)

/-- The paper-facing almost-commutativity estimate: first the triangle-inequality version, then
the quantitative step bound coming from the two local zero-stability certificates. -/
def almostCommuteBound (D : RiemannSiegelGabckeRecursionData) : Prop :=
  |D.commutator| ≤ |D.next.refinementStep| + |D.current.refinementStep| ∧
    |D.commutator| ≤
      (2 * D.next.deltaSup) / D.next.m + (2 * D.current.deltaSup) / D.current.m

end RiemannSiegelGabckeRecursionData

open RiemannSiegelGabckeRecursionData

/-- Expanding the two recursion composites shows that the commutator is exactly the difference
of the two local refinement steps; triangle inequality plus the local-zero-stability step bounds
then control it quantitatively.
    prop:cdim-rs-gabcke-recursions-almost-commute -/
theorem paper_cdim_rs_gabcke_recursions_almost_commute
    (D : RiemannSiegelGabckeRecursionData) : D.almostCommuteBound := by
  have htriangle' :
      |D.commutator| ≤ |D.next.refinementStep| + |-D.current.refinementStep| := by
    simpa [RiemannSiegelGabckeRecursionData.commutator,
      RiemannSiegelGabckeRecursionData.advanceAtK,
      RiemannSiegelGabckeRecursionData.advanceAtK1,
      RiemannSiegelGabckeRecursionData.refineAtCurrent,
      RiemannSiegelGabckeRecursionData.baseAtCurrent,
      RiemannSiegelGabckeLocalRefinement.refinementStep, sub_eq_add_neg] using
      abs_add_le D.next.refinementStep (-D.current.refinementStep)
  have htriangle :
      |D.commutator| ≤ |D.next.refinementStep| + |D.current.refinementStep| := by
    calc
      |D.commutator| ≤ |D.next.refinementStep| + |-D.current.refinementStep| := htriangle'
      _ = |D.next.refinementStep| + |D.current.refinementStep| := by rw [abs_neg]
  refine ⟨htriangle, ?_⟩
  exact le_trans htriangle (add_le_add D.next.refinementStep_bound D.current.refinementStep_bound)

end Omega.CircleDimension
