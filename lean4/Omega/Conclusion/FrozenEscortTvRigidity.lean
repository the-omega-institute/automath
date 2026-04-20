import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Full `L¹` distance between two finite laws. -/
def frozenEscortL1Distance {α : Type*} [Fintype α] (escortLaw uniformLaw : α → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset α) fun x => |escortLaw x - uniformLaw x|

/-- Total escort mass carried by the maximal fiber. -/
def frozenEscortMassOnMaxFiber {α : Type*} (maxFiber : Finset α) (escortLaw : α → ℝ) : ℝ :=
  Finset.sum maxFiber escortLaw

/-- Total mass of the escort law. -/
def frozenEscortTotalMass {α : Type*} [Fintype α] (escortLaw : α → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset α) escortLaw

/-- Concrete frozen-escort data on a finite state space. The escort law agrees with the uniform
law on the maximal fiber, the uniform law vanishes off that fiber, and the escort law has total
mass `1`. -/
structure FrozenEscortTvRigidityData where
  α : Type*
  instFintype : Fintype α
  instDecEq : DecidableEq α
  maxFiber : Finset α
  escortLaw : α → ℝ
  uniformLaw : α → ℝ
  tvDistance : ℝ
  massOnMaxFiber : ℝ
  exponentialGap : ℝ
  tvDistance_def : tvDistance = frozenEscortL1Distance escortLaw uniformLaw
  uniform_off_max : ∀ x, x ∉ maxFiber → uniformLaw x = 0
  escort_eq_uniform_on_max : ∀ x, x ∈ maxFiber → escortLaw x = uniformLaw x
  escort_nonneg : ∀ x, 0 ≤ escortLaw x
  escort_total_mass : frozenEscortTotalMass escortLaw = 1
  massOnMaxFiber_def : massOnMaxFiber = frozenEscortMassOnMaxFiber maxFiber escortLaw
  missingMass_exp_bound : 1 - massOnMaxFiber ≤ Real.exp (-exponentialGap)

attribute [instance] FrozenEscortTvRigidityData.instFintype
attribute [instance] FrozenEscortTvRigidityData.instDecEq

private lemma frozenEscort_tv_split_zero_on_max (h : FrozenEscortTvRigidityData) :
    Finset.sum h.maxFiber (fun x => |h.escortLaw x - h.uniformLaw x|) = 0 := by
  calc
    Finset.sum h.maxFiber (fun x => |h.escortLaw x - h.uniformLaw x|) =
        Finset.sum h.maxFiber (fun _ => (0 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [h.escort_eq_uniform_on_max x hx]
      simp
    _ = 0 := by simp

private lemma frozenEscort_tv_split_off_max (h : FrozenEscortTvRigidityData) :
    Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber)
        (fun x => |h.escortLaw x - h.uniformLaw x|) =
      Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hx' : x ∉ h.maxFiber := by
    simpa using hx
  rw [h.uniform_off_max x hx', sub_zero, abs_of_nonneg (h.escort_nonneg x)]

private lemma frozenEscort_mass_split (h : FrozenEscortTvRigidityData) :
    Finset.sum h.maxFiber h.escortLaw +
        Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw =
      1 := by
  have hfilter :
      (Finset.univ.filter fun x : h.α => x ∈ h.maxFiber) = h.maxFiber := by
    ext x
    simp
  calc
    Finset.sum h.maxFiber h.escortLaw +
        Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw =
          Finset.sum (Finset.univ.filter fun x : h.α => x ∈ h.maxFiber) h.escortLaw +
            Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw := by
              rw [hfilter]
    _ = Finset.sum (Finset.univ : Finset h.α) h.escortLaw := by
          exact Finset.sum_filter_add_sum_filter_not
            (s := (Finset.univ : Finset h.α)) (p := fun x => x ∈ h.maxFiber) (f := h.escortLaw)
    _ = 1 := by simpa [frozenEscortTotalMass] using h.escort_total_mass

/-- In the frozen regime, the escort/uniform `L¹` distance is exactly the missing mass off the
maximal fiber, and the recorded gap estimate bounds that missing mass exponentially.
    thm:conclusion-frozen-escort-tv-rigidity -/
theorem paper_conclusion_frozen_escort_tv_rigidity (h : FrozenEscortTvRigidityData) :
    h.tvDistance = 1 - h.massOnMaxFiber ∧ h.tvDistance ≤ Real.exp (-h.exponentialGap) := by
  have htv :
      h.tvDistance =
        Finset.sum h.maxFiber (fun x => |h.escortLaw x - h.uniformLaw x|) +
          Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber)
            (fun x => |h.escortLaw x - h.uniformLaw x|) := by
    rw [h.tvDistance_def]
    unfold frozenEscortL1Distance
    have hfilter :
        (Finset.univ.filter fun x : h.α => x ∈ h.maxFiber) = h.maxFiber := by
      ext x
      simp
    calc
      Finset.sum (Finset.univ : Finset h.α) (fun x => |h.escortLaw x - h.uniformLaw x|) =
          Finset.sum (Finset.univ.filter fun x : h.α => x ∈ h.maxFiber)
              (fun x => |h.escortLaw x - h.uniformLaw x|) +
            Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber)
              (fun x => |h.escortLaw x - h.uniformLaw x|) := by
                symm
                exact Finset.sum_filter_add_sum_filter_not
                  (s := (Finset.univ : Finset h.α))
                  (p := fun x => x ∈ h.maxFiber)
                  (f := fun x => |h.escortLaw x - h.uniformLaw x|)
      _ =
          Finset.sum h.maxFiber (fun x => |h.escortLaw x - h.uniformLaw x|) +
            Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber)
              (fun x => |h.escortLaw x - h.uniformLaw x|) := by
                rw [hfilter]
  have hmass :
      Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw =
        1 - h.massOnMaxFiber := by
    rw [h.massOnMaxFiber_def, frozenEscortMassOnMaxFiber]
    have hsplit := frozenEscort_mass_split h
    linarith
  constructor
  · calc
      h.tvDistance =
          Finset.sum h.maxFiber (fun x => |h.escortLaw x - h.uniformLaw x|) +
            Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber)
              (fun x => |h.escortLaw x - h.uniformLaw x|) := htv
      _ = 0 + Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw := by
            rw [frozenEscort_tv_split_zero_on_max h, frozenEscort_tv_split_off_max h]
      _ = 1 - h.massOnMaxFiber := by rw [zero_add, hmass]
  · rw [show h.tvDistance = 1 - h.massOnMaxFiber by
      calc
        h.tvDistance =
            Finset.sum h.maxFiber (fun x => |h.escortLaw x - h.uniformLaw x|) +
              Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber)
                (fun x => |h.escortLaw x - h.uniformLaw x|) := htv
        _ = 0 + Finset.sum (Finset.univ.filter fun x => x ∉ h.maxFiber) h.escortLaw := by
              rw [frozenEscort_tv_split_zero_on_max h, frozenEscort_tv_split_off_max h]
        _ = 1 - h.massOnMaxFiber := by rw [zero_add, hmass]]
    exact h.missingMass_exp_bound

end Omega.Conclusion
