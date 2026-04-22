import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete data for a finite diagonal-plus-rank-one kernel whose secular roots produce
Sturm--Cauchy eigenfunctions. -/
structure DiagonalRateSturmCauchyEigenbasisData where
  State : Type
  instFintypeState : Fintype State
  Mode : Type
  instFintypeMode : Fintype Mode
  t : State → ℝ
  κ : ℝ
  z : Mode → ℝ
  hkappa : ∀ x, t x ≠ κ
  hpole : ∀ i x, t x ≠ z i
  secular : ∀ i, ∑ x, 1 / (t x - z i) = 1
  distinct : ∀ ⦃i j⦄, i ≠ j → z i ≠ z j

attribute [instance] DiagonalRateSturmCauchyEigenbasisData.instFintypeState
attribute [instance] DiagonalRateSturmCauchyEigenbasisData.instFintypeMode

/-- The diagonal-plus-rank-one kernel written in operator form. -/
def diagonalRateSturmCauchyKernelApply (D : DiagonalRateSturmCauchyEigenbasisData)
    (f : D.State → ℝ) (x : D.State) : ℝ :=
  D.t x * f x - (D.t x - D.κ) * ∑ y, (1 / (D.t y - D.κ)) * f y

/-- Closed-form stationary weights for the weighted orthogonality relation. -/
def diagonalRateSturmCauchyStationaryWeight (D : DiagonalRateSturmCauchyEigenbasisData)
    (x : D.State) : ℝ :=
  (1 / (D.t x - D.κ)) ^ 2

/-- The explicit Sturm--Cauchy eigenfunction attached to a secular root. -/
def diagonalRateSturmCauchyEigenfunction (D : DiagonalRateSturmCauchyEigenbasisData)
    (i : D.Mode) (x : D.State) : ℝ :=
  (D.t x - D.κ) / (D.t x - D.z i)

/-- Weighted inner product determined by the stationary weights. -/
def diagonalRateSturmCauchyWeightedInner (D : DiagonalRateSturmCauchyEigenbasisData)
    (f g : D.State → ℝ) : ℝ :=
  ∑ x, diagonalRateSturmCauchyStationaryWeight D x * f x * g x

/-- The paper-facing Sturm--Cauchy eigenbasis package. -/
def DiagonalRateSturmCauchyEigenbasisStatement
    (D : DiagonalRateSturmCauchyEigenbasisData) : Prop :=
  (∀ i x,
      diagonalRateSturmCauchyKernelApply D (diagonalRateSturmCauchyEigenfunction D i) x =
        D.z i * diagonalRateSturmCauchyEigenfunction D i x) ∧
    ∀ i j, i ≠ j →
      diagonalRateSturmCauchyWeightedInner D
          (diagonalRateSturmCauchyEigenfunction D i)
          (diagonalRateSturmCauchyEigenfunction D j) = 0

private lemma diagonalRateSturmCauchy_average_eq_one
    (D : DiagonalRateSturmCauchyEigenbasisData) (i : D.Mode) :
    ∑ y, (1 / (D.t y - D.κ)) * diagonalRateSturmCauchyEigenfunction D i y = 1 := by
  calc
    ∑ y, (1 / (D.t y - D.κ)) * diagonalRateSturmCauchyEigenfunction D i y
        = ∑ y, 1 / (D.t y - D.z i) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            unfold diagonalRateSturmCauchyEigenfunction
            have hk : D.t y - D.κ ≠ 0 := sub_ne_zero.mpr (D.hkappa y)
            have hz : D.t y - D.z i ≠ 0 := sub_ne_zero.mpr (D.hpole i y)
            field_simp [hk, hz]
    _ = 1 := D.secular i

private lemma diagonalRateSturmCauchy_weighted_term
    (D : DiagonalRateSturmCauchyEigenbasisData) (i j : D.Mode) (x : D.State) :
    diagonalRateSturmCauchyStationaryWeight D x *
        diagonalRateSturmCauchyEigenfunction D i x *
        diagonalRateSturmCauchyEigenfunction D j x =
      1 / ((D.t x - D.z i) * (D.t x - D.z j)) := by
  unfold diagonalRateSturmCauchyStationaryWeight diagonalRateSturmCauchyEigenfunction
  have hk : D.t x - D.κ ≠ 0 := sub_ne_zero.mpr (D.hkappa x)
  have hi : D.t x - D.z i ≠ 0 := sub_ne_zero.mpr (D.hpole i x)
  have hj : D.t x - D.z j ≠ 0 := sub_ne_zero.mpr (D.hpole j x)
  field_simp [hk, hi, hj]

private lemma diagonalRateSturmCauchy_partial_fraction {t a b : ℝ}
    (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) :
    1 / ((t - a) * (t - b)) = (1 / (a - b)) * (1 / (t - a) - 1 / (t - b)) := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hta' : t - a ≠ 0 := sub_ne_zero.mpr hta
  have htb' : t - b ≠ 0 := sub_ne_zero.mpr htb
  field_simp [hab', hta', htb']
  linarith

/-- Paper label: `thm:pom-diagonal-rate-sturm-cauchy-eigenbasis`. -/
theorem paper_pom_diagonal_rate_sturm_cauchy_eigenbasis
    (D : DiagonalRateSturmCauchyEigenbasisData) : DiagonalRateSturmCauchyEigenbasisStatement D := by
  refine ⟨?_, ?_⟩
  · intro i x
    have hAvg : ∑ y, (1 / (D.t y - D.κ)) * diagonalRateSturmCauchyEigenfunction D i y = 1 :=
      diagonalRateSturmCauchy_average_eq_one D i
    unfold diagonalRateSturmCauchyKernelApply
    rw [hAvg]
    unfold diagonalRateSturmCauchyEigenfunction
    have hz : D.t x - D.z i ≠ 0 := sub_ne_zero.mpr (D.hpole i x)
    field_simp [hz]
    ring
  · intro i j hij
    unfold diagonalRateSturmCauchyWeightedInner
    calc
      ∑ x,
          diagonalRateSturmCauchyStationaryWeight D x *
              diagonalRateSturmCauchyEigenfunction D i x *
            diagonalRateSturmCauchyEigenfunction D j x =
          ∑ x, 1 / ((D.t x - D.z i) * (D.t x - D.z j)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact diagonalRateSturmCauchy_weighted_term D i j x
      _ = ∑ x, (1 / (D.z i - D.z j)) *
            (1 / (D.t x - D.z i) - 1 / (D.t x - D.z j)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              apply diagonalRateSturmCauchy_partial_fraction
              · exact D.distinct hij
              · exact D.hpole i x
              · exact D.hpole j x
      _ = (1 / (D.z i - D.z j)) *
            ∑ x, (1 / (D.t x - D.z i) - 1 / (D.t x - D.z j)) := by
              rw [Finset.mul_sum]
      _ = (1 / (D.z i - D.z j)) *
            ((∑ x, 1 / (D.t x - D.z i)) - ∑ x, 1 / (D.t x - D.z j)) := by
              rw [Finset.sum_sub_distrib]
      _ = (1 / (D.z i - D.z j)) * (1 - 1) := by rw [D.secular i, D.secular j]
      _ = 0 := by ring

end

end Omega.POM
