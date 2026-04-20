import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiFixedFreezingEscortGroundstateTvIdentity

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Expectation of an observable against a finite law. -/
def xiObservableExpectation {α : Type*} [Fintype α] (μ : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, μ x * f x

/-- Concrete finite data for the fixed-freezing escort observable-collapse theorem. -/
structure XiFixedFreezingEscortObservableData where
  α : Type*
  instFintype : Fintype α
  instDecEq : DecidableEq α
  maxFiber : Finset α
  escortLaw : α → ℝ
  groundLaw : α → ℝ
  observable : α → ℝ
  supNorm : ℝ
  groundConst : ℝ
  tvDistance : ℝ
  massOnMaxFiber : ℝ
  exponentialGap : ℝ
  supNorm_nonneg : 0 ≤ supNorm
  tvDistance_def : tvDistance = Finset.sum Finset.univ (fun x => |escortLaw x - groundLaw x|)
  ground_off_max : ∀ x, x ∉ maxFiber → groundLaw x = 0
  escort_nonneg : ∀ x, 0 ≤ escortLaw x
  escort_total_mass : Finset.sum Finset.univ escortLaw = 1
  ground_total_mass : Finset.sum Finset.univ groundLaw = 1
  massOnMaxFiber_def : massOnMaxFiber = Finset.sum maxFiber escortLaw
  observable_bound : ∀ x, |observable x| ≤ supNorm
  observable_on_max : ∀ x, x ∈ maxFiber → observable x = groundConst
  tv_exponential_bound : tvDistance ≤ Real.exp (-exponentialGap)

attribute [instance] XiFixedFreezingEscortObservableData.instFintype
attribute [instance] XiFixedFreezingEscortObservableData.instDecEq

namespace XiFixedFreezingEscortObservableData

/-- Paper-facing observable-collapse statement. -/
def exponentialObservableCollapse (D : XiFixedFreezingEscortObservableData) : Prop :=
  |xiObservableExpectation D.escortLaw D.observable -
      xiObservableExpectation D.groundLaw D.observable|
      ≤ 2 * D.supNorm * Real.exp (-D.exponentialGap) ∧
    (xiObservableExpectation D.escortLaw D.observable -
        xiObservableExpectation D.groundLaw D.observable =
      Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
        (fun x => D.escortLaw x * (D.observable x - D.groundConst)))

end XiFixedFreezingEscortObservableData

private lemma ground_expectation_eq_groundConst (D : XiFixedFreezingEscortObservableData) :
    xiObservableExpectation D.groundLaw D.observable = D.groundConst := by
  have hsplit :
      xiObservableExpectation D.groundLaw D.observable =
        Finset.sum D.maxFiber (fun x => D.groundLaw x * D.observable x) +
          Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
            (fun x => D.groundLaw x * D.observable x) := by
    have hdecomp := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset D.α)) (p := fun x => x ∈ D.maxFiber)
      (f := fun x => D.groundLaw x * D.observable x)
    have hfilter :
        (Finset.univ.filter fun x : D.α => x ∈ D.maxFiber) = D.maxFiber := by
      ext x
      simp
    simpa [xiObservableExpectation, hfilter] using hdecomp.symm
  have hoff :
      Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
        (fun x => D.groundLaw x * D.observable x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hx' : x ∉ D.maxFiber := by simpa using hx
    simp [D.ground_off_max x hx']
  have hmass :
      Finset.sum D.maxFiber D.groundLaw = 1 := by
    have hdecomp := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset D.α)) (p := fun x => x ∈ D.maxFiber) (f := D.groundLaw)
    have hfilter :
        (Finset.univ.filter fun x : D.α => x ∈ D.maxFiber) = D.maxFiber := by
      ext x
      simp
    have hoffMass :
        Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber) D.groundLaw = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hx' : x ∉ D.maxFiber := by simpa using hx
      simp [D.ground_off_max x hx']
    have htotal : Finset.sum (Finset.univ : Finset D.α) D.groundLaw = 1 := by
      simpa using D.ground_total_mass
    rw [htotal] at hdecomp
    rw [hfilter, hoffMass, add_zero] at hdecomp
    exact hdecomp
  calc
    xiObservableExpectation D.groundLaw D.observable
        = Finset.sum D.maxFiber (fun x => D.groundLaw x * D.observable x) := by
          rw [hsplit, hoff, add_zero]
    _ = Finset.sum D.maxFiber (fun x => D.groundLaw x * D.groundConst) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [D.observable_on_max x hx]
    _ = Finset.sum D.maxFiber D.groundLaw * D.groundConst := by rw [Finset.sum_mul]
    _ = D.groundConst := by rw [hmass, one_mul]

private lemma expectation_diff_le_supNorm_l1 (D : XiFixedFreezingEscortObservableData) :
    |xiObservableExpectation D.escortLaw D.observable -
        xiObservableExpectation D.groundLaw D.observable|
      ≤ D.supNorm * D.tvDistance := by
  have hrew :
      xiObservableExpectation D.escortLaw D.observable -
          xiObservableExpectation D.groundLaw D.observable =
        ∑ x : D.α, (D.escortLaw x - D.groundLaw x) * D.observable x := by
    unfold xiObservableExpectation
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring
  rw [hrew]
  calc
    |∑ x : D.α, (D.escortLaw x - D.groundLaw x) * D.observable x|
        ≤ ∑ x : D.α, |(D.escortLaw x - D.groundLaw x) * D.observable x| := by
            simpa using
              (abs_sum_le_sum_abs (s := (Finset.univ : Finset D.α))
                (f := fun x => (D.escortLaw x - D.groundLaw x) * D.observable x))
    _ = ∑ x : D.α, |D.escortLaw x - D.groundLaw x| * |D.observable x| := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [abs_mul]
    _ ≤ ∑ x : D.α, |D.escortLaw x - D.groundLaw x| * D.supNorm := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact mul_le_mul_of_nonneg_left (D.observable_bound x) (abs_nonneg _)
    _ = D.supNorm * ∑ x : D.α, |D.escortLaw x - D.groundLaw x| := by
          calc
            ∑ x : D.α, |D.escortLaw x - D.groundLaw x| * D.supNorm
                = (∑ x : D.α, |D.escortLaw x - D.groundLaw x|) * D.supNorm := by
                    rw [Finset.sum_mul]
            _ = D.supNorm * ∑ x : D.α, |D.escortLaw x - D.groundLaw x| := by ring
    _ = D.supNorm * D.tvDistance := by rw [D.tvDistance_def]

private lemma escort_offMax_mass (D : XiFixedFreezingEscortObservableData) :
    Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber) D.escortLaw = 1 - D.massOnMaxFiber := by
  have hdecomp := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset D.α)) (p := fun x => x ∈ D.maxFiber) (f := D.escortLaw)
  have hfilter :
      (Finset.univ.filter fun x : D.α => x ∈ D.maxFiber) = D.maxFiber := by
    ext x
    simp
  have htotal : Finset.sum (Finset.univ : Finset D.α) D.escortLaw = 1 := by
    simpa using D.escort_total_mass
  rw [htotal] at hdecomp
  rw [hfilter, ← D.massOnMaxFiber_def] at hdecomp
  linarith

private lemma expectation_diff_eq_offMax (D : XiFixedFreezingEscortObservableData) :
      (xiObservableExpectation D.escortLaw D.observable -
        xiObservableExpectation D.groundLaw D.observable =
      Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
        (fun x => D.escortLaw x * (D.observable x - D.groundConst))) := by
  have hsplitEscort :
      xiObservableExpectation D.escortLaw D.observable =
        Finset.sum D.maxFiber (fun x => D.escortLaw x * D.observable x) +
          Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
            (fun x => D.escortLaw x * D.observable x) := by
    have hdecomp := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset D.α)) (p := fun x => x ∈ D.maxFiber)
      (f := fun x => D.escortLaw x * D.observable x)
    have hfilter :
        (Finset.univ.filter fun x : D.α => x ∈ D.maxFiber) = D.maxFiber := by
      ext x
      simp
    simpa [xiObservableExpectation, hfilter] using hdecomp.symm
  have hmax :
      Finset.sum D.maxFiber (fun x => D.escortLaw x * D.observable x) = D.massOnMaxFiber * D.groundConst := by
    calc
      Finset.sum D.maxFiber (fun x => D.escortLaw x * D.observable x)
          = Finset.sum D.maxFiber (fun x => D.escortLaw x * D.groundConst) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [D.observable_on_max x hx]
      _ = Finset.sum D.maxFiber D.escortLaw * D.groundConst := by rw [Finset.sum_mul]
      _ = D.massOnMaxFiber * D.groundConst := by rw [← D.massOnMaxFiber_def]
  calc
    xiObservableExpectation D.escortLaw D.observable -
        xiObservableExpectation D.groundLaw D.observable
        = (Finset.sum D.maxFiber (fun x => D.escortLaw x * D.observable x) +
              Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
                (fun x => D.escortLaw x * D.observable x)) -
            D.groundConst := by rw [hsplitEscort, ground_expectation_eq_groundConst D]
    _ = D.massOnMaxFiber * D.groundConst +
          Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
            (fun x => D.escortLaw x * D.observable x) -
            D.groundConst := by rw [hmax]
    _ = Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
          (fun x => D.escortLaw x * D.observable x) -
          (1 - D.massOnMaxFiber) * D.groundConst := by ring
    _ = Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
          (fun x => D.escortLaw x * D.observable x) -
          Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber) D.escortLaw * D.groundConst := by
            rw [escort_offMax_mass D]
    _ = Finset.sum (Finset.univ.filter fun x => x ∉ D.maxFiber)
          (fun x => D.escortLaw x * (D.observable x - D.groundConst)) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring

/-- The frozen escort observable statistics collapse exponentially to the groundstate value, and
if the observable is constant on the maximal layer then the entire error is carried by the
off-groundstate mass.
    thm:xi-fixed-freezing-escort-bounded-observable-collapse -/
theorem paper_xi_fixed_freezing_escort_bounded_observable_collapse
    (D : XiFixedFreezingEscortObservableData) :
    XiFixedFreezingEscortObservableData.exponentialObservableCollapse D := by
  rw [XiFixedFreezingEscortObservableData.exponentialObservableCollapse]
  refine ⟨?_, expectation_diff_eq_offMax D⟩
  calc
    |xiObservableExpectation D.escortLaw D.observable -
        xiObservableExpectation D.groundLaw D.observable|
        ≤ D.supNorm * D.tvDistance := expectation_diff_le_supNorm_l1 D
    _ ≤ D.supNorm * Real.exp (-D.exponentialGap) := by
          exact mul_le_mul_of_nonneg_left D.tv_exponential_bound D.supNorm_nonneg
    _ ≤ 2 * D.supNorm * Real.exp (-D.exponentialGap) := by
          have hnonneg : 0 ≤ D.supNorm * Real.exp (-D.exponentialGap) := by
            exact mul_nonneg D.supNorm_nonneg (Real.exp_pos _).le
          calc
            D.supNorm * Real.exp (-D.exponentialGap) ≤
                D.supNorm * Real.exp (-D.exponentialGap) +
                  D.supNorm * Real.exp (-D.exponentialGap) := by
                    nlinarith
            _ = 2 * D.supNorm * Real.exp (-D.exponentialGap) := by ring

end Omega.Zeta
