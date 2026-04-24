import Mathlib

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite cover data for the paper-facing fiber trace-moment statement. -/
structure PomFiberTraceMomentsRationalityData where
  Y : Type*
  X : Type*
  instFintypeY : Fintype Y
  instDecidableEqY : DecidableEq Y
  instFintypeX : Fintype X
  instDecidableEqX : DecidableEq X
  fiberMap : X → Y
  observable : X → ℚ
  surj : Function.Surjective fiberMap

attribute [instance] PomFiberTraceMomentsRationalityData.instFintypeY
attribute [instance] PomFiberTraceMomentsRationalityData.instDecidableEqY
attribute [instance] PomFiberTraceMomentsRationalityData.instFintypeX
attribute [instance] PomFiberTraceMomentsRationalityData.instDecidableEqX

namespace PomFiberTraceMomentsRationalityData

def fiber (D : PomFiberTraceMomentsRationalityData) (y : D.Y) : Finset D.X :=
  Finset.univ.filter fun x => D.fiberMap x = y

def fiberCard (D : PomFiberTraceMomentsRationalityData) (y : D.Y) : ℕ :=
  (D.fiber y).card

def fiberPowerSum (D : PomFiberTraceMomentsRationalityData) (m : ℕ) (y : D.Y) : ℚ :=
  Finset.sum (D.fiber y) fun x => D.observable x ^ m

/-- Chapter-local trace model: the fiber power sum is the trace readout. -/
def fiberTrace (D : PomFiberTraceMomentsRationalityData) (m : ℕ) (y : D.Y) : ℚ :=
  D.fiberPowerSum m y

def mean (D : PomFiberTraceMomentsRationalityData) (y : D.Y) : ℚ :=
  D.fiberPowerSum 1 y / D.fiberCard y

def variance (D : PomFiberTraceMomentsRationalityData) (y : D.Y) : ℚ :=
  D.fiberPowerSum 2 y / D.fiberCard y - D.mean y ^ 2

def l2Error (D : PomFiberTraceMomentsRationalityData) (y : D.Y) (a : ℚ) : ℚ :=
  Finset.sum (D.fiber y) fun x => (D.observable x - a) ^ 2

def traceMomentsRational (D : PomFiberTraceMomentsRationalityData) : Prop :=
  ∀ m y, ∃ q : ℚ, D.fiberPowerSum m y = q ∧ D.fiberTrace m y = q

def meanVarianceRational (D : PomFiberTraceMomentsRationalityData) : Prop :=
  ∀ y, ∃ μ v : ℚ, D.mean y = μ ∧ D.variance y = v

/-- Exact finite-uniform conditional-expectation identity for squared loss. -/
def uniformPosteriorL2Optimal (D : PomFiberTraceMomentsRationalityData) : Prop :=
  ∀ y a,
    D.l2Error y a = D.l2Error y (D.mean y) + (D.fiberCard y : ℚ) * (D.mean y - a) ^ 2

lemma fiber_nonempty (D : PomFiberTraceMomentsRationalityData) (y : D.Y) : (D.fiber y).Nonempty := by
  classical
  rcases D.surj y with ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  simp [fiber]

lemma fiberCard_pos (D : PomFiberTraceMomentsRationalityData) (y : D.Y) : 0 < D.fiberCard y := by
  classical
  exact Finset.card_pos.mpr (D.fiber_nonempty y)

lemma fiberCard_mul_mean (D : PomFiberTraceMomentsRationalityData) (y : D.Y) :
    (D.fiberCard y : ℚ) * D.mean y = Finset.sum (D.fiber y) fun x => D.observable x := by
  have hcard_ne : (D.fiberCard y : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos y)
  unfold mean fiberPowerSum
  field_simp [hcard_ne]

lemma sum_sub_mean_eq_zero (D : PomFiberTraceMomentsRationalityData) (y : D.Y) :
    Finset.sum (D.fiber y) (fun x => D.observable x - D.mean y) = 0 := by
  calc
    Finset.sum (D.fiber y) (fun x => D.observable x - D.mean y)
        = Finset.sum (D.fiber y) (fun x => D.observable x) -
            Finset.sum (D.fiber y) (fun _ => D.mean y) := by
            rw [Finset.sum_sub_distrib]
    _ = Finset.sum (D.fiber y) (fun x => D.observable x) - (D.fiberCard y : ℚ) * D.mean y := by
          simp [fiberCard]
    _ = Finset.sum (D.fiber y) (fun x => D.observable x) -
          Finset.sum (D.fiber y) (fun x => D.observable x) := by
          rw [D.fiberCard_mul_mean y]
    _ = 0 := sub_self _

lemma l2Error_mean_decomposition (D : PomFiberTraceMomentsRationalityData) (y : D.Y) (a : ℚ) :
    D.l2Error y a = D.l2Error y (D.mean y) + (D.fiberCard y : ℚ) * (D.mean y - a) ^ 2 := by
  have hcross :
      Finset.sum (D.fiber y) (fun x => 2 * (D.observable x - D.mean y) * (D.mean y - a)) = 0 := by
    calc
      Finset.sum (D.fiber y) (fun x => 2 * (D.observable x - D.mean y) * (D.mean y - a))
          = Finset.sum (D.fiber y) (fun x => (2 * (D.mean y - a)) * (D.observable x - D.mean y)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = (2 * (D.mean y - a)) * Finset.sum (D.fiber y) (fun x => D.observable x - D.mean y) := by
            rw [Finset.mul_sum]
      _ = 0 := by simp [D.sum_sub_mean_eq_zero y]
  calc
    D.l2Error y a
        = Finset.sum (D.fiber y) fun x =>
            (D.observable x - D.mean y) ^ 2 +
              2 * (D.observable x - D.mean y) * (D.mean y - a) +
              (D.mean y - a) ^ 2 := by
              unfold l2Error
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
    _ = Finset.sum (D.fiber y) (fun x => (D.observable x - D.mean y) ^ 2) +
          Finset.sum (D.fiber y) (fun x => 2 * (D.observable x - D.mean y) * (D.mean y - a)) +
          Finset.sum (D.fiber y) (fun _ => (D.mean y - a) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = D.l2Error y (D.mean y) + 0 + Finset.sum (D.fiber y) (fun _ => (D.mean y - a) ^ 2) := by
          simp [l2Error, hcross]
    _ = D.l2Error y (D.mean y) + (D.fiberCard y : ℚ) * (D.mean y - a) ^ 2 := by
          simp [fiberCard]

end PomFiberTraceMomentsRationalityData

open PomFiberTraceMomentsRationalityData

/-- Paper label: `thm:pom-fiber-trace-moments-rationality`. -/
theorem paper_pom_fiber_trace_moments_rationality (D : PomFiberTraceMomentsRationalityData) :
    D.traceMomentsRational ∧ D.meanVarianceRational ∧ D.uniformPosteriorL2Optimal := by
  refine ⟨?_, ?_, ?_⟩
  · intro m y
    exact ⟨D.fiberPowerSum m y, rfl, rfl⟩
  · intro y
    exact ⟨D.mean y, D.variance y, rfl, rfl⟩
  · exact D.l2Error_mean_decomposition

end Omega.POM
