import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.HzomCriticalZerosJointSpectrumComb

namespace Omega.OperatorAlgebra

/-- The distinguished critical abscissa in the HZOM functional equation. -/
noncomputable def hzomCriticalAbscissa : ℝ := 1 / 2

/-- Scalar weight contributed by the commuting polar part at real part `σ`. -/
noncomputable def hzomPolarWeight (κ σ : ℝ) : ℝ :=
  Real.exp ((σ - hzomCriticalAbscissa) * Real.log κ)

/-- A nontrivial HZOM zero event consists of the joint-spectrum zero condition together with the
commuting polar factor being exactly `1`. -/
def hzomCommutingPolarZeroEvent (lam theta κ σ t : ℝ) : Prop :=
  hzomZeroAt lam theta t ∧ hzomPolarWeight κ σ = 1

/-- Reflection symmetry of the nontrivial HZOM zero set across the critical line. -/
def hzomReflectionSymmetricZeroSet (lam theta κ : ℝ) : Prop :=
  ∀ {σ t}, hzomCommutingPolarZeroEvent lam theta κ σ t →
    hzomCommutingPolarZeroEvent lam theta κ (1 - σ) t

/-- Strict contraction of the commuting polar factor. -/
def hzomStrictPolarContraction (κ : ℝ) : Prop :=
  0 < κ ∧ κ < 1

/-- The strict contraction hypothesis rules out nontrivial zero events in `Re(s) > 1/2`. -/
def hzomRightHalfPlaneZeroFree (lam theta κ : ℝ) : Prop :=
  ∀ {σ t}, hzomCriticalAbscissa < σ → ¬ hzomCommutingPolarZeroEvent lam theta κ σ t

/-- Reflection symmetry then forces every nontrivial zero event onto `Re(s) = 1/2`. -/
def hzomCriticalLineConcentration (lam theta κ : ℝ) : Prop :=
  ∀ {σ t}, hzomCommutingPolarZeroEvent lam theta κ σ t → σ = hzomCriticalAbscissa

private theorem hzom_right_half_plane_zero_free_of_strict_contraction
    {lam theta κ : ℝ} (hκ : hzomStrictPolarContraction κ) :
    hzomRightHalfPlaneZeroFree lam theta κ := by
  intro σ t hσ hZero
  have hκ0 : 0 < κ := hκ.1
  have hκ1 : κ < 1 := hκ.2
  have hlog : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  have hshift : 0 < σ - hzomCriticalAbscissa := by
    dsimp [hzomCriticalAbscissa] at hσ ⊢
    linarith
  have hexponent : (σ - hzomCriticalAbscissa) * Real.log κ < 0 := by
    nlinarith
  have hweight_lt : hzomPolarWeight κ σ < 1 := by
    simpa [hzomPolarWeight] using Real.exp_lt_one_iff.mpr hexponent
  exact ne_of_lt hweight_lt hZero.2

/-- Paper-facing HZOM wrapper for commuting polar decompositions: strict contraction forbids
nontrivial zero events in the open right half-plane, and reflection symmetry upgrades this to
critical-line concentration of all nontrivial zero events.
    thm:op-algebra-hzom-commuting-polar-forces-critical-line -/
theorem paper_op_algebra_hzom_commuting_polar_forces_critical_line
    {lam theta κ : ℝ} (hκ : hzomStrictPolarContraction κ)
    (hreflect : hzomReflectionSymmetricZeroSet lam theta κ) :
    hzomRightHalfPlaneZeroFree lam theta κ ∧ hzomCriticalLineConcentration lam theta κ := by
  have hFree : hzomRightHalfPlaneZeroFree lam theta κ :=
    hzom_right_half_plane_zero_free_of_strict_contraction hκ
  refine ⟨hFree, ?_⟩
  intro σ t hZero
  by_cases hlt : σ < hzomCriticalAbscissa
  · exfalso
    have hReflected := hreflect hZero
    have hReflectedPos : hzomCriticalAbscissa < 1 - σ := by
      dsimp [hzomCriticalAbscissa] at hlt ⊢
      nlinarith
    exact hFree (σ := 1 - σ) (t := t) hReflectedPos hReflected
  · by_cases hgt : hzomCriticalAbscissa < σ
    · exfalso
      exact hFree (σ := σ) (t := t) hgt hZero
    · have hge : hzomCriticalAbscissa ≤ σ := le_of_not_gt hlt
      have hle : σ ≤ hzomCriticalAbscissa := le_of_not_gt hgt
      dsimp [hzomCriticalAbscissa] at hge hle ⊢
      linarith

end Omega.OperatorAlgebra
