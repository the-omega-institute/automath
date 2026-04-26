import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- Concrete inhomogeneous fiber-posterior data: a finite family of active local moves together
with a positive activity profile on the three-step windows they touch. -/
structure FiberInhomConditionalUniformityData where
  localCount : ℕ
  active : Finset (Fin localCount)
  activity : Fin (localCount + 2) → ℝ
  hactivity : ∀ i, 0 < activity i

namespace FiberInhomConditionalUniformityData

def prop_pom_fiber_inhom_conditional_uniformity_localWeight
    (D : FiberInhomConditionalUniformityData) (j : Fin D.localCount) : ℝ :=
  D.activity ⟨j.1 + 1, by omega⟩ * D.activity ⟨j.1 + 2, by omega⟩ / D.activity ⟨j.1, by omega⟩

def prop_pom_fiber_inhom_conditional_uniformity_weight
    (D : FiberInhomConditionalUniformityData) (S : Finset (Fin D.localCount)) : ℝ :=
  ∏ j ∈ S, prop_pom_fiber_inhom_conditional_uniformity_localWeight D j

def prop_pom_fiber_inhom_conditional_uniformity_normalizer
    (D : FiberInhomConditionalUniformityData) : ℝ :=
  Finset.sum D.active.powerset
    (fun S => prop_pom_fiber_inhom_conditional_uniformity_weight D S)

def prop_pom_fiber_inhom_conditional_uniformity_posteriorMass
    (D : FiberInhomConditionalUniformityData) (S : Finset (Fin D.localCount)) : ℝ :=
  prop_pom_fiber_inhom_conditional_uniformity_weight D S /
    prop_pom_fiber_inhom_conditional_uniformity_normalizer D

def prop_pom_fiber_inhom_conditional_uniformity_posteriorUniform
    (D : FiberInhomConditionalUniformityData) : Prop :=
  ∀ S ∈ D.active.powerset, ∀ T ∈ D.active.powerset,
    prop_pom_fiber_inhom_conditional_uniformity_posteriorMass D S =
      prop_pom_fiber_inhom_conditional_uniformity_posteriorMass D T

def prop_pom_fiber_inhom_conditional_uniformity_logLinear
    (D : FiberInhomConditionalUniformityData) : Prop :=
  ∀ j ∈ D.active,
    Real.log (D.activity ⟨j.1, by omega⟩) =
      Real.log (D.activity ⟨j.1 + 1, by omega⟩) +
        Real.log (D.activity ⟨j.1 + 2, by omega⟩)

def statement (D : FiberInhomConditionalUniformityData) : Prop :=
  (∀ S ∈ D.active.powerset,
      prop_pom_fiber_inhom_conditional_uniformity_posteriorMass D S =
        prop_pom_fiber_inhom_conditional_uniformity_weight D S /
          prop_pom_fiber_inhom_conditional_uniformity_normalizer D) ∧
    (prop_pom_fiber_inhom_conditional_uniformity_posteriorUniform D ↔
      ∀ j ∈ D.active, prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1) ∧
    ((∀ j ∈ D.active, prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1) ↔
      prop_pom_fiber_inhom_conditional_uniformity_logLinear D)

lemma prop_pom_fiber_inhom_conditional_uniformity_localWeight_pos
    (D : FiberInhomConditionalUniformityData) (j : Fin D.localCount) :
    0 < prop_pom_fiber_inhom_conditional_uniformity_localWeight D j := by
  unfold prop_pom_fiber_inhom_conditional_uniformity_localWeight
  exact div_pos
    (mul_pos (D.hactivity ⟨j.1 + 1, by omega⟩) (D.hactivity ⟨j.1 + 2, by omega⟩))
    (D.hactivity ⟨j.1, by omega⟩)

lemma prop_pom_fiber_inhom_conditional_uniformity_weight_pos
    (D : FiberInhomConditionalUniformityData) (S : Finset (Fin D.localCount)) :
    0 < prop_pom_fiber_inhom_conditional_uniformity_weight D S := by
  classical
  unfold prop_pom_fiber_inhom_conditional_uniformity_weight
  refine Finset.prod_pos ?_
  intro j hj
  exact D.prop_pom_fiber_inhom_conditional_uniformity_localWeight_pos j

lemma prop_pom_fiber_inhom_conditional_uniformity_normalizer_pos
    (D : FiberInhomConditionalUniformityData) :
    0 < prop_pom_fiber_inhom_conditional_uniformity_normalizer D := by
  classical
  have hmem : (∅ : Finset (Fin D.localCount)) ∈ D.active.powerset := by simp
  have hle :
      prop_pom_fiber_inhom_conditional_uniformity_weight D ∅ ≤
        prop_pom_fiber_inhom_conditional_uniformity_normalizer D := by
    unfold prop_pom_fiber_inhom_conditional_uniformity_normalizer
    simpa using Finset.single_le_sum
      (fun S hS => (D.prop_pom_fiber_inhom_conditional_uniformity_weight_pos S).le) hmem
  have hzero : 0 < prop_pom_fiber_inhom_conditional_uniformity_weight D ∅ := by
    simpa using D.prop_pom_fiber_inhom_conditional_uniformity_weight_pos (∅ : Finset (Fin D.localCount))
  exact lt_of_lt_of_le hzero hle

lemma prop_pom_fiber_inhom_conditional_uniformity_weight_eq_one_of_all_one
    (D : FiberInhomConditionalUniformityData)
    (hflat : ∀ j ∈ D.active, prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1)
    {S : Finset (Fin D.localCount)} (hS : S ⊆ D.active) :
    prop_pom_fiber_inhom_conditional_uniformity_weight D S = 1 := by
  classical
  unfold prop_pom_fiber_inhom_conditional_uniformity_weight
  refine Finset.prod_eq_one ?_
  intro j hj
  exact hflat j (hS hj)

lemma prop_pom_fiber_inhom_conditional_uniformity_uniform_iff
    (D : FiberInhomConditionalUniformityData) :
    prop_pom_fiber_inhom_conditional_uniformity_posteriorUniform D ↔
      ∀ j ∈ D.active, prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1 := by
  constructor
  · intro hunif j hj
    have hsingle : ({j} : Finset (Fin D.localCount)) ∈ D.active.powerset := by
      simp [hj]
    have hempty : (∅ : Finset (Fin D.localCount)) ∈ D.active.powerset := by simp
    have hEq := hunif {j} hsingle ∅ hempty
    have hnorm_ne :
        prop_pom_fiber_inhom_conditional_uniformity_normalizer D ≠ 0 :=
      (D.prop_pom_fiber_inhom_conditional_uniformity_normalizer_pos).ne'
    have hEq' :
        prop_pom_fiber_inhom_conditional_uniformity_localWeight D j /
            prop_pom_fiber_inhom_conditional_uniformity_normalizer D =
          1 / prop_pom_fiber_inhom_conditional_uniformity_normalizer D := by
      simpa [prop_pom_fiber_inhom_conditional_uniformity_posteriorMass,
        prop_pom_fiber_inhom_conditional_uniformity_weight] using hEq
    have hEq'' := (div_eq_div_iff hnorm_ne hnorm_ne).mp hEq'
    have hnorm_pos := D.prop_pom_fiber_inhom_conditional_uniformity_normalizer_pos
    have : prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1 := by
      nlinarith
    exact this
  · intro hflat
    intro S hS T hT
    have hS' :
        prop_pom_fiber_inhom_conditional_uniformity_weight D S = 1 :=
      D.prop_pom_fiber_inhom_conditional_uniformity_weight_eq_one_of_all_one hflat
        (Finset.mem_powerset.mp hS)
    have hT' :
        prop_pom_fiber_inhom_conditional_uniformity_weight D T = 1 :=
      D.prop_pom_fiber_inhom_conditional_uniformity_weight_eq_one_of_all_one hflat
        (Finset.mem_powerset.mp hT)
    simp [prop_pom_fiber_inhom_conditional_uniformity_posteriorMass, hS', hT']

lemma prop_pom_fiber_inhom_conditional_uniformity_localWeight_eq_one_iff_log
    (D : FiberInhomConditionalUniformityData) (j : Fin D.localCount) :
    prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1 ↔
      Real.log (D.activity ⟨j.1, by omega⟩) =
        Real.log (D.activity ⟨j.1 + 1, by omega⟩) +
          Real.log (D.activity ⟨j.1 + 2, by omega⟩) := by
  let a0 := D.activity ⟨j.1, by omega⟩
  let a1 := D.activity ⟨j.1 + 1, by omega⟩
  let a2 := D.activity ⟨j.1 + 2, by omega⟩
  have ha0 : 0 < a0 := by simpa [a0] using D.hactivity ⟨j.1, by omega⟩
  have ha1 : 0 < a1 := by simpa [a1] using D.hactivity ⟨j.1 + 1, by omega⟩
  have ha2 : 0 < a2 := by simpa [a2] using D.hactivity ⟨j.1 + 2, by omega⟩
  constructor
  · intro h
    have hmul : a0 = a1 * a2 := by
      have h' : a1 * a2 / a0 = 1 := by
        simpa [prop_pom_fiber_inhom_conditional_uniformity_localWeight, a0, a1, a2] using h
      field_simp [ha0.ne'] at h'
      nlinarith
    have hgoal : Real.log a0 = Real.log a1 + Real.log a2 := by
      rw [hmul, Real.log_mul ha1.ne' ha2.ne']
    simpa [a0, a1, a2] using hgoal
  · intro h
    have h' : Real.log a0 = Real.log a1 + Real.log a2 := by
      simpa [a0, a1, a2] using h
    have hexp := congrArg Real.exp h'
    have hmul : a0 = a1 * a2 := by
      simpa [Real.exp_add, Real.exp_log ha0, Real.exp_log ha1, Real.exp_log ha2] using hexp
    have hgoal : a1 * a2 / a0 = 1 := by
      rw [hmul]
      field_simp [ha0.ne']
    simpa [prop_pom_fiber_inhom_conditional_uniformity_localWeight, a0, a1, a2] using hgoal

lemma prop_pom_fiber_inhom_conditional_uniformity_log_iff
    (D : FiberInhomConditionalUniformityData) :
    (∀ j ∈ D.active, prop_pom_fiber_inhom_conditional_uniformity_localWeight D j = 1) ↔
      prop_pom_fiber_inhom_conditional_uniformity_logLinear D := by
  constructor
  · intro hflat j hj
    exact (D.prop_pom_fiber_inhom_conditional_uniformity_localWeight_eq_one_iff_log j).mp
      (hflat j hj)
  · intro hlog j hj
    exact (D.prop_pom_fiber_inhom_conditional_uniformity_localWeight_eq_one_iff_log j).mpr
      (hlog j hj)

end FiberInhomConditionalUniformityData

/-- Paper label: `prop:pom-fiber-inhom-conditional-uniformity`. The finite posterior on the
independent-set side factors through the local activity ratios, and the resulting hard-core law is
uniform exactly when every active local weight is `1`, equivalently when the log activities satisfy
`u_j = u_{j+1} + u_{j+2}` on every active window. -/
theorem paper_pom_fiber_inhom_conditional_uniformity (D : Omega.POM.FiberInhomConditionalUniformityData) :
    D.statement := by
  refine ⟨?_, D.prop_pom_fiber_inhom_conditional_uniformity_uniform_iff,
    D.prop_pom_fiber_inhom_conditional_uniformity_log_iff⟩
  intro S hS
  rfl

end

end Omega.POM
