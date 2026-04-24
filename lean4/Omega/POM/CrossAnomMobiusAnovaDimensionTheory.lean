import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Omega.POM

open Finset
open scoped BigOperators

/-- Concrete finite-axis data for the Möbius--ANOVA dimension count.  The quantity
`groupCardMinusOne i` is `|G_i| - 1`, so the full axis size is `groupCardMinusOne i + 1`. -/
structure pom_cross_anom_mobius_anova_dimension_theory_data where
  k : ℕ
  groupCardMinusOne : Fin k → ℕ

/-- Free coordinates on the pure `S`-component: one choice for each nontrivial coordinate along
the axes in `S`. -/
def pom_cross_anom_mobius_anova_dimension_theory_pure_dimension
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) (S : Finset (Fin D.k)) : ℕ :=
  ∏ i ∈ S, D.groupCardMinusOne i

/-- Total normalized coordinate count on the full product: all product coordinates except the
basepoint. -/
def pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) : ℕ :=
  (∏ i : Fin D.k, (D.groupCardMinusOne i + 1)) - 1

/-- Axis-decomposable coordinates are the one-body terms. -/
def pom_cross_anom_mobius_anova_dimension_theory_axis_dimension
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) : ℕ :=
  Finset.sum
    (((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => S.card = 1))
    (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S)

/-- Two-body visible coordinates are the one-body and two-body pure components. -/
def pom_cross_anom_mobius_anova_dimension_theory_visible_two_body_dimension
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) : ℕ :=
  pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D +
    Finset.sum
      (((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => S.card = 2))
      (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S)

/-- Hidden coordinates are the three-body and higher pure components. -/
def pom_cross_anom_mobius_anova_dimension_theory_hidden_three_body_dimension
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) : ℕ :=
  Finset.sum
    (((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => 3 ≤ S.card))
    (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S)

/-- Packaged publication-facing dimension identities for the concrete finite-axis model. -/
def pom_cross_anom_mobius_anova_dimension_theory_statement
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) : Prop :=
  (∀ S : Finset (Fin D.k),
      pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S =
        ∏ i ∈ S, D.groupCardMinusOne i) ∧
    (Finset.sum
        ((Finset.univ : Finset (Fin D.k)).powerset.erase ∅)
        (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) =
      pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension D) ∧
    (pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D =
      ∑ i : Fin D.k, D.groupCardMinusOne i) ∧
    (pom_cross_anom_mobius_anova_dimension_theory_visible_two_body_dimension D =
      pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D +
        Finset.sum
          (((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => S.card = 2))
          (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S)) ∧
    (pom_cross_anom_mobius_anova_dimension_theory_hidden_three_body_dimension D =
      Finset.sum
        (((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => 3 ≤ S.card))
        (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S))

lemma pom_cross_anom_mobius_anova_dimension_theory_singleton_filter
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) :
    (Finset.univ.image fun i : Fin D.k => ({i} : Finset (Fin D.k))) =
      (((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => S.card = 1)) := by
  classical
  ext S
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, -, rfl⟩
    simp
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hmem, hcard⟩
    rcases Finset.mem_erase.mp hmem with ⟨_, _⟩
    rcases Finset.card_eq_one.mp hcard with ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

lemma pom_cross_anom_mobius_anova_dimension_theory_nonempty_sum
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) :
    Finset.sum
        ((Finset.univ : Finset (Fin D.k)).powerset.erase ∅)
        (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) =
      pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension D := by
  classical
  have hprod :
      ∏ i : Fin D.k, (D.groupCardMinusOne i + 1) =
        ∑ S ∈ (Finset.univ : Finset (Fin D.k)).powerset,
          pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S := by
    simpa [pom_cross_anom_mobius_anova_dimension_theory_pure_dimension] using
      (Finset.prod_add_one (s := (Finset.univ : Finset (Fin D.k))) (f := D.groupCardMinusOne))
  have hsplit :
      Finset.sum
          ((Finset.univ : Finset (Fin D.k)).powerset.erase ∅)
          (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) + 1 =
        ∑ S ∈ (Finset.univ : Finset (Fin D.k)).powerset,
          pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S := by
    simpa [pom_cross_anom_mobius_anova_dimension_theory_pure_dimension] using
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (Fin D.k)).powerset)
        (a := ∅)
        (f := pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D)
        (by simp))
  have hmain :
      Finset.sum
          ((Finset.univ : Finset (Fin D.k)).powerset.erase ∅)
          (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) + 1 =
        ∏ i : Fin D.k, (D.groupCardMinusOne i + 1) := by
    calc
      Finset.sum
          ((Finset.univ : Finset (Fin D.k)).powerset.erase ∅)
          (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) + 1 =
        ∑ S ∈ (Finset.univ : Finset (Fin D.k)).powerset,
          pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S := hsplit
      _ = ∏ i : Fin D.k, (D.groupCardMinusOne i + 1) := hprod.symm
  exact Nat.eq_sub_of_add_eq hmain

lemma pom_cross_anom_mobius_anova_dimension_theory_axis_sum
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) :
    pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D =
      ∑ i : Fin D.k, D.groupCardMinusOne i := by
  classical
  unfold pom_cross_anom_mobius_anova_dimension_theory_axis_dimension
  rw [← pom_cross_anom_mobius_anova_dimension_theory_singleton_filter D]
  rw [Finset.sum_image]
  · simp [pom_cross_anom_mobius_anova_dimension_theory_pure_dimension]
  · intro i _ j _ hij
    simpa using hij

/-- Paper label: `thm:pom-cross-anom-mobius-anova-dimension-theory`.
The concrete finite-axis model records the Möbius--ANOVA pure `S`-component coordinates by the
nontrivial choices on the axes in `S`, sums those pure dimensions over all nonempty subsets to
recover the normalized ambient dimension, and isolates the one-body, visible two-body, and hidden
three-body-plus contributions by filtering on the subset size. -/
theorem paper_pom_cross_anom_mobius_anova_dimension_theory
    (D : pom_cross_anom_mobius_anova_dimension_theory_data) :
    pom_cross_anom_mobius_anova_dimension_theory_statement D := by
  refine ⟨(fun S => rfl), pom_cross_anom_mobius_anova_dimension_theory_nonempty_sum D,
    pom_cross_anom_mobius_anova_dimension_theory_axis_sum D, rfl, rfl⟩

end Omega.POM
