import Mathlib.Tactic

namespace Omega.SPG.PolycubeIsoperimetryUpper

open Finset

variable {α : Type*}

/-- Sum of face counts bounded by `2n · |U|`.
    thm:spg-dyadic-polyclube-discrete-isoperimetry -/
theorem sum_card_le_mul_card {β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → Finset β) (n : ℕ)
    (h : ∀ q ∈ U, (f q).card ≤ 2 * n) :
    (∑ q ∈ U, (f q).card) ≤ 2 * n * U.card := by
  have hsum : (∑ q ∈ U, (f q).card) ≤ ∑ _q ∈ U, 2 * n :=
    Finset.sum_le_sum (fun q hq => h q hq)
  have hconst : (∑ _q ∈ U, (2 * n : ℕ)) = U.card * (2 * n) := by
    rw [Finset.sum_const, smul_eq_mul]
  rw [hconst] at hsum
  linarith

/-- `|⋃ f q| ≤ ∑ |f q|`.
    thm:spg-dyadic-polyclube-discrete-isoperimetry -/
theorem biUnion_card_le_sum_card [DecidableEq α] {β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → Finset β) :
    (U.biUnion f).card ≤ ∑ q ∈ U, (f q).card :=
  Finset.card_biUnion_le

/-- Polycube boundary upper bound: `|⋃ f q| ≤ 2n · |U|`.
    thm:spg-dyadic-polyclube-discrete-isoperimetry -/
theorem polycube_boundary_upper_bound [DecidableEq α] {β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → Finset β) (n : ℕ)
    (h : ∀ q ∈ U, (f q).card ≤ 2 * n) :
    (U.biUnion f).card ≤ 2 * n * U.card :=
  (biUnion_card_le_sum_card U f).trans (sum_card_le_mul_card U f n h)

/-- External faces upper bound (any sub-family of the union).
    thm:spg-dyadic-polyclube-discrete-isoperimetry -/
theorem external_faces_upper_bound [DecidableEq α] {β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → Finset β) (n : ℕ) (F : Finset β)
    (hF : F ⊆ U.biUnion f)
    (h : ∀ q ∈ U, (f q).card ≤ 2 * n) :
    F.card ≤ 2 * n * U.card :=
  (Finset.card_le_card hF).trans (polycube_boundary_upper_bound U f n h)

/-- Paper package (upper bound only).
    thm:spg-dyadic-polyclube-discrete-isoperimetry -/
theorem paper_spg_dyadic_polyclube_discrete_isoperimetry_upper
    [DecidableEq α] {β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → Finset β) (n : ℕ) (F : Finset β)
    (hF : F ⊆ U.biUnion f) (h : ∀ q ∈ U, (f q).card ≤ 2 * n) :
    F.card ≤ 2 * n * U.card :=
  external_faces_upper_bound U f n F hF h

end Omega.SPG.PolycubeIsoperimetryUpper
