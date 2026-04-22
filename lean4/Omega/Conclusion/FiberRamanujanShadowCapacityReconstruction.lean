import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Concrete finite fiber data together with the Ramanujan-shadow tail counts. -/
structure conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data where
  fiber : Type
  [fiberFintype : Fintype fiber]
  [fiberDecidableEq : DecidableEq fiber]
  fiberSize : fiber → ℕ
  maxFiberSize : ℕ
  fiberSize_pos : ∀ x, 1 ≤ fiberSize x
  fiberSize_le_max : ∀ x, fiberSize x ≤ maxFiberSize
  ramanujanShadowTail : ℕ → ℤ
  ramanujanShadowTail_spec : ∀ t, ramanujanShadowTail t = Fintype.card {x : fiber // t ≤ fiberSize x}

attribute [instance] conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data.fiberFintype
attribute [instance] conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data.fiberDecidableEq

/-- Exact multiplicity of the fiber-size layer `k + 1`. -/
def conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (k : ℕ) : ℤ :=
  Fintype.card {x : D.fiber // D.fiberSize x = k + 1}

/-- Histogram recovered from adjacent Ramanujan-shadow tail counts. -/
def conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (k : ℕ) : ℤ :=
  D.ramanujanShadowTail (k + 1) - D.ramanujanShadowTail (k + 2)

/-- Finite weighted capacity curve attached to the exact fiber histogram. -/
def conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (t : ℕ) : ℤ :=
  Finset.sum (Finset.range D.maxFiberSize) fun k =>
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D k *
      (Nat.min (k + 1) t : ℤ)

/-- Second-difference recovery of the histogram from the capacity curve. -/
def conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (k : ℕ) : ℤ :=
  (conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D (k + 1) -
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D k) -
    (conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D (k + 2) -
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D (k + 1))

/-- Proposition-level package for the fiber/capacity/Ramanujan-shadow reconstruction layer. -/
def conclusion_fiber_ramanujan_shadow_capacity_reconstruction_statement
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) : Prop :=
  (∀ t,
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D t =
      Finset.sum (Finset.range D.maxFiberSize) fun k =>
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D k *
          (Nat.min (k + 1) t : ℤ)) ∧
    (∀ k,
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D k =
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D k) ∧
    (∀ h : ℕ → ℤ,
      (∀ k,
        h k =
          conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D k) →
      h =
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D)

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_card_eq_tail_sub_tail_succ
    {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun x => f x = k)).card =
      (Finset.univ.filter fun x => k ≤ f x).card -
        (Finset.univ.filter fun x => k + 1 ≤ f x).card := by
  let A : Finset α := Finset.univ.filter fun x => k ≤ f x
  let B : Finset α := Finset.univ.filter fun x => k + 1 ≤ f x
  have hBA : B ⊆ A := by
    intro x hx
    simp [A, B] at hx ⊢
    omega
  have hsplit : A \ B = Finset.univ.filter (fun x => f x = k) := by
    ext x
    simp [A, B]
    omega
  have hcard :
      (Finset.univ.filter (fun x => f x = k)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram_eq_shadow
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (k : ℕ) :
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D k =
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D k := by
  unfold conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram
  rw [D.ramanujanShadowTail_spec (k + 1), D.ramanujanShadowTail_spec (k + 2)]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => D.fiberSize x = k + 1) (by
    intro x
    simp)]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k + 1 ≤ D.fiberSize x) (by
    intro x
    simp)]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k + 2 ≤ D.fiberSize x) (by
    intro x
    simp)]
  have hle :
      (Finset.univ.filter fun x => k + 2 ≤ D.fiberSize x).card ≤
        (Finset.univ.filter fun x => k + 1 ≤ D.fiberSize x).card := by
    exact Finset.card_le_card (by
      intro x hx
      simp at hx ⊢
      omega)
  change ((Finset.univ.filter fun x => D.fiberSize x = k + 1).card : ℤ) =
    ((Finset.univ.filter fun x => k + 1 ≤ D.fiberSize x).card : ℤ) -
      ((Finset.univ.filter fun x => k + 2 ≤ D.fiberSize x).card : ℤ)
  rw [← Int.ofNat_sub hle]
  exact_mod_cast
    (conclusion_fiber_ramanujan_shadow_capacity_reconstruction_card_eq_tail_sub_tail_succ
      (f := D.fiberSize) (k := k + 1))

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram_vanishes
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) {k : ℕ}
    (hk : D.maxFiberSize ≤ k) :
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D k = 0 := by
  unfold conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram
  norm_num
  apply Nat.eq_zero_of_not_pos
  intro hpos
  rw [Fintype.card_pos_iff] at hpos
  rcases hpos with ⟨⟨x, hx⟩⟩
  have hle := D.fiberSize_le_max x
  omega

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_basis_second_difference
    (j k : ℕ) :
    (((Nat.min (j + 1) (k + 1) : ℤ) - (Nat.min (j + 1) k : ℤ)) -
        (((Nat.min (j + 1) (k + 2) : ℤ) - (Nat.min (j + 1) (k + 1) : ℤ)))) =
      if j = k then 1 else 0 := by
  by_cases hlt : j < k
  · have hmin1 : Nat.min (j + 1) (k + 1) = j + 1 := Nat.min_eq_left (by omega)
    have hmin2 : Nat.min (j + 1) k = j + 1 := Nat.min_eq_left (by omega)
    have hmin3 : Nat.min (j + 1) (k + 2) = j + 1 := Nat.min_eq_left (by omega)
    simp [hmin1, hmin2, hmin3, hlt.ne]
  · by_cases heq : j = k
    · subst heq
      norm_num
    · have hgt : k < j := by omega
      have hmin1 : Nat.min (j + 1) (k + 1) = k + 1 := Nat.min_eq_right (by omega)
      have hmin2 : Nat.min (j + 1) k = k := Nat.min_eq_right (by omega)
      have hmin3 : Nat.min (j + 1) (k + 2) = k + 2 := Nat.min_eq_right (by omega)
      simp [hmin1, hmin2, hmin3, heq]

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_step_difference
    (j k : ℕ) :
    ((Nat.min (j + 1) (k + 1) : ℤ) - (Nat.min (j + 1) k : ℤ)) =
      if k ≤ j then 1 else 0 := by
  by_cases h : k ≤ j
  · have hmin1 : Nat.min (j + 1) (k + 1) = k + 1 := Nat.min_eq_right (by omega)
    have hmin2 : Nat.min (j + 1) k = k := Nat.min_eq_right (by omega)
    simp [hmin2, h]
  · have hlt : j < k := by omega
    have hmin1 : Nat.min (j + 1) (k + 1) = j + 1 := Nat.min_eq_left (by omega)
    have hmin2 : Nat.min (j + 1) k = j + 1 := Nat.min_eq_left (by omega)
    simp [hmin1, hmin2, h]

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_delta_eq_tail_sum
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (k : ℕ) :
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D (k + 1) -
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve D k =
        Finset.sum (Finset.range D.maxFiberSize) fun j =>
          conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
            (if k ≤ j then 1 else 0) := by
  unfold conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
          (Nat.min (j + 1) (k + 1) : ℤ) -
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
          (Nat.min (j + 1) k : ℤ)
      =
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
          (((Nat.min (j + 1) (k + 1) : ℤ) - (Nat.min (j + 1) k : ℤ))) := by
            ring
    _ =
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
          (if k ≤ j then 1 else 0) := by
            rw [conclusion_fiber_ramanujan_shadow_capacity_reconstruction_step_difference]

private theorem conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_eq_exact
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) (k : ℕ) :
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D k =
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D k := by
  unfold conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram
  rw [conclusion_fiber_ramanujan_shadow_capacity_reconstruction_delta_eq_tail_sum,
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_delta_eq_tail_sum]
  rw [← Finset.sum_sub_distrib]
  have hrewrite :
      Finset.sum (Finset.range D.maxFiberSize) (fun j =>
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
          (if k ≤ j then 1 else 0) -
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
          (if k + 1 ≤ j then 1 else 0)) =
        Finset.sum (Finset.range D.maxFiberSize) fun j =>
          conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D j *
            (if j = k then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hkj : k ≤ j
    · by_cases hksj : k + 1 ≤ j
      · have hne : j ≠ k := by omega
        rw [if_pos hkj, if_pos hksj, if_neg hne]
        ring
      · have heq : j = k := by omega
        rw [if_pos hkj, if_neg hksj, if_pos heq]
        ring
    · have hnot : ¬ k + 1 ≤ j := by omega
      have hne : j ≠ k := by omega
      rw [if_neg hkj, if_neg hnot, if_neg hne]
      ring
  rw [hrewrite]
  by_cases hk : k < D.maxFiberSize
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j hj1 hj2
      simp [hj2]
    · intro hknot
      exfalso
      exact hknot (Finset.mem_range.mpr hk)
  · have hvanish :
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram D k = 0 := by
      exact
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram_vanishes D
          (Nat.le_of_not_gt hk)
    rw [Finset.sum_eq_zero]
    · simp [hvanish]
    · intro j hj
      have hjne : j ≠ k := by
        intro hEq
        subst hEq
        exact hk (Finset.mem_range.mp hj)
      simp [hjne]

/-- Paper label: `thm:conclusion-fiber-ramanujan-shadow-capacity-reconstruction`. -/
theorem paper_conclusion_fiber_ramanujan_shadow_capacity_reconstruction
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) :
    conclusion_fiber_ramanujan_shadow_capacity_reconstruction_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    unfold conclusion_fiber_ramanujan_shadow_capacity_reconstruction_capacity_curve
    apply Finset.sum_congr rfl
    intro k hk
    rw [conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram_eq_shadow D k]
  · intro k
    rw [conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_eq_exact D k,
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram_eq_shadow D k]
  · intro h hh
    funext k
    rw [hh k, conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_eq_exact D k,
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_exact_histogram_eq_shadow D k]

end Omega.Conclusion
