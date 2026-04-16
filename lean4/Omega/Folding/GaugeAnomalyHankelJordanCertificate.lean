import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Omega.Folding.AutocovarianceSeedValues

namespace Omega.Folding

open Matrix
open Omega.Folding.AutocovarianceSeedValues

/-- Chapter-local carrier for the gauge-anomaly autocovariance Hankel certificate. The actual
certificate data is fixed by the closed-form autocovariance seeds already proved in
`AutocovarianceSeedValues`. -/
structure GaugeAnomalyAutocovarianceData where

namespace GaugeAnomalyAutocovarianceData

/-- The explicit `3 × 3` Hankel matrix built from the autocovariance seeds
`c₁, …, c₅`. -/
def hankel3 (_ : GaugeAnomalyAutocovarianceData) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(17 / 324 : ℚ), (25 / 648 : ℚ), (7 / 648 : ℚ);
    (25 / 648 : ℚ), (7 / 648 : ℚ), (7 / 648 : ℚ);
    (7 / 648 : ℚ), (7 / 648 : ℚ), (11 / 5184 : ℚ)]

/-- The explicit `4 × 4` Hankel matrix built from the autocovariance seeds
`c₁, …, c₇`. -/
def hankel4 (_ : GaugeAnomalyAutocovarianceData) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(17 / 324 : ℚ), (25 / 648 : ℚ), (7 / 648 : ℚ), (7 / 648 : ℚ);
    (25 / 648 : ℚ), (7 / 648 : ℚ), (7 / 648 : ℚ), (11 / 5184 : ℚ);
    (7 / 648 : ℚ), (7 / 648 : ℚ), (11 / 5184 : ℚ), (31 / 10368 : ℚ);
    (7 / 648 : ℚ), (11 / 5184 : ℚ), (31 / 10368 : ℚ), (1 / 2592 : ℚ)]

/-- The first three Hankel columns, used both for the rank lower bound and the recurrence
factorization. -/
def columnWindow (_ : GaugeAnomalyAutocovarianceData) : Matrix (Fin 4) (Fin 3) ℚ :=
  !![(17 / 324 : ℚ), (25 / 648 : ℚ), (7 / 648 : ℚ);
    (25 / 648 : ℚ), (7 / 648 : ℚ), (7 / 648 : ℚ);
    (7 / 648 : ℚ), (7 / 648 : ℚ), (11 / 5184 : ℚ);
    (7 / 648 : ℚ), (11 / 5184 : ℚ), (31 / 10368 : ℚ)]

/-- The recurrence factor encoding
`c_{n+3} = (1/8)c_n + (1/4)c_{n+1} - (1/2)c_{n+2}`. -/
def recurrenceFactor (_ : GaugeAnomalyAutocovarianceData) : Matrix (Fin 3) (Fin 4) ℚ :=
  !![(1 : ℚ), 0, 0, (1 / 8 : ℚ);
    0, (1 : ℚ), 0, (1 / 4 : ℚ);
    0, 0, (1 : ℚ), (-1 / 2 : ℚ)]

/-- Paper-facing determinant certificate for the `3 × 3` Hankel block. -/
def hankelDet3Nonzero (h : GaugeAnomalyAutocovarianceData) : Prop :=
  h.hankel3.det ≠ 0

/-- Paper-facing determinant certificate for the `4 × 4` Hankel block. -/
def hankelDet4Zero (h : GaugeAnomalyAutocovarianceData) : Prop :=
  h.hankel4.det = 0

/-- Paper-facing rank certificate for the gauge-anomaly Hankel matrix. -/
def hankelRankEqThree (h : GaugeAnomalyAutocovarianceData) : Prop :=
  h.hankel4.rank = 3

private def fin3To4 : Fin 3 → Fin 4 := Fin.castLE (by decide)

private theorem autoCov_six : autoCov 6 = 31 / 10368 := by
  simp [autoCov]
  ring

private theorem autoCov_seven : autoCov 7 = 1 / 2592 := by
  simp [autoCov]
  ring

private theorem hankel3_det (h : GaugeAnomalyAutocovarianceData) :
    h.hankel3.det = -1 / 2985984 := by
  simp [GaugeAnomalyAutocovarianceData.hankel3, Matrix.det_fin_three]
  ring

private theorem hankel4_last_column_formula (h : GaugeAnomalyAutocovarianceData) (i : Fin 4) :
    h.hankel4 i 3 =
      (1 / 8 : ℚ) * h.hankel4 i 0 + (1 / 4 : ℚ) * h.hankel4 i 1
        - (1 / 2 : ℚ) * h.hankel4 i 2 := by
  fin_cases i
  · change (7 / 648 : ℚ) = (1 / 8 : ℚ) * (17 / 324 : ℚ) + (1 / 4 : ℚ) * (25 / 648 : ℚ) -
      (1 / 2 : ℚ) * (7 / 648 : ℚ)
    norm_num
  · change (11 / 5184 : ℚ) = (1 / 8 : ℚ) * (25 / 648 : ℚ) + (1 / 4 : ℚ) * (7 / 648 : ℚ) -
      (1 / 2 : ℚ) * (7 / 648 : ℚ)
    norm_num
  · change (31 / 10368 : ℚ) = (1 / 8 : ℚ) * (7 / 648 : ℚ) + (1 / 4 : ℚ) * (7 / 648 : ℚ) -
      (1 / 2 : ℚ) * (11 / 5184 : ℚ)
    norm_num
  · change (1 / 2592 : ℚ) = (1 / 8 : ℚ) * (7 / 648 : ℚ) + (1 / 4 : ℚ) * (11 / 5184 : ℚ) -
      (1 / 2 : ℚ) * (31 / 10368 : ℚ)
    norm_num

private theorem hankel4_update_last_column (h : GaugeAnomalyAutocovarianceData) :
    h.hankel4.updateCol 3 (fun k ↦ ∑ i : Fin 4, (![1 / 8, 1 / 4, -1 / 2, 0] : Fin 4 → ℚ) i *
      h.hankel4 k i) = h.hankel4 := by
  ext i j
  fin_cases j
  · simp [Matrix.updateCol]
  · simp [Matrix.updateCol]
  · simp [Matrix.updateCol]
  · simp [Matrix.updateCol, Fin.sum_univ_four, hankel4_last_column_formula]
    ring

private theorem hankel4_det_zero (h : GaugeAnomalyAutocovarianceData) :
    h.hankel4.det = 0 := by
  calc
    h.hankel4.det = (h.hankel4.updateCol 3
        (fun k ↦ ∑ i : Fin 4, (![1 / 8, 1 / 4, -1 / 2, 0] : Fin 4 → ℚ) i * h.hankel4 k i)).det := by
      rw [hankel4_update_last_column]
    _ = ((![1 / 8, 1 / 4, -1 / 2, 0] : Fin 4 → ℚ) 3) * h.hankel4.det := by
      simpa using Matrix.det_updateCol_sum h.hankel4 3
        (![1 / 8, 1 / 4, -1 / 2, 0] : Fin 4 → ℚ)
    _ = (0 : ℚ) * h.hankel4.det := by
      have hc : ((![1 / 8, 1 / 4, -1 / 2, 0] : Fin 4 → ℚ) 3) = 0 := by native_decide
      rw [hc]
    _ = 0 := by ring

private theorem hankel4_factorization (h : GaugeAnomalyAutocovarianceData) :
    h.hankel4 = h.columnWindow * h.recurrenceFactor := by
  ext i j
  fin_cases j
  · simp [GaugeAnomalyAutocovarianceData.hankel4, GaugeAnomalyAutocovarianceData.columnWindow,
      GaugeAnomalyAutocovarianceData.recurrenceFactor, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [GaugeAnomalyAutocovarianceData.hankel4, GaugeAnomalyAutocovarianceData.columnWindow,
      GaugeAnomalyAutocovarianceData.recurrenceFactor, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [GaugeAnomalyAutocovarianceData.hankel4, GaugeAnomalyAutocovarianceData.columnWindow,
      GaugeAnomalyAutocovarianceData.recurrenceFactor, Matrix.mul_apply, Fin.sum_univ_three]
  · fin_cases i <;>
      simp [GaugeAnomalyAutocovarianceData.hankel4, GaugeAnomalyAutocovarianceData.columnWindow,
        GaugeAnomalyAutocovarianceData.recurrenceFactor, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring

private theorem hankel3_rank_eq_three (h : GaugeAnomalyAutocovarianceData) :
    h.hankel3.rank = 3 := by
  have hunit : IsUnit h.hankel3 := by
    exact
      (Matrix.isUnit_iff_isUnit_det (A := h.hankel3)).2
        (isUnit_iff_ne_zero.mpr (by rw [hankel3_det]; norm_num))
  simpa using Matrix.rank_of_isUnit h.hankel3 hunit

private theorem hankel3_eq_columnWindow_submatrix (h : GaugeAnomalyAutocovarianceData) :
    h.hankel3 = h.columnWindow.submatrix fin3To4 (Equiv.refl (Fin 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem columnWindow_transpose_eq_hankel4_transpose_submatrix
    (h : GaugeAnomalyAutocovarianceData) :
    h.columnWindow.transpose =
      h.hankel4.transpose.submatrix fin3To4 (Equiv.refl (Fin 4)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem columnWindow_rank_eq_three (h : GaugeAnomalyAutocovarianceData) :
    h.columnWindow.rank = 3 := by
  have h3rank : h.hankel3.rank = 3 := hankel3_rank_eq_three h
  have hsub :
      h.hankel3.rank ≤ h.columnWindow.rank := by
    rw [hankel3_eq_columnWindow_submatrix]
    simpa using
      (Matrix.rank_submatrix_le (f := fin3To4) (e := Equiv.refl (Fin 3)) h.columnWindow)
  have hupper : h.columnWindow.rank ≤ 3 := Matrix.rank_le_width h.columnWindow
  omega

private theorem hankel4_rank_le_three (h : GaugeAnomalyAutocovarianceData) :
    h.hankel4.rank ≤ 3 := by
  calc
    h.hankel4.rank = (h.columnWindow * h.recurrenceFactor).rank := by
      rw [hankel4_factorization]
    _ ≤ h.columnWindow.rank := Matrix.rank_mul_le_left _ _
    _ = 3 := columnWindow_rank_eq_three h

private theorem hankel4_rank_ge_three (h : GaugeAnomalyAutocovarianceData) :
    3 ≤ h.hankel4.rank := by
  have hcolrank : h.columnWindow.rank = 3 := columnWindow_rank_eq_three h
  have hsubT :
      h.columnWindow.transpose.rank ≤ h.hankel4.transpose.rank := by
    rw [columnWindow_transpose_eq_hankel4_transpose_submatrix]
    simpa using
      (Matrix.rank_submatrix_le (f := fin3To4) (e := Equiv.refl (Fin 4)) h.hankel4.transpose)
  have hsub : h.columnWindow.rank ≤ h.hankel4.rank := by
    simpa [Matrix.rank_transpose] using hsubT
  rw [hcolrank] at hsub
  exact hsub

/-- Explicit Hankel certificate for the gauge-anomaly autocovariance sequence:
`det H^(3) ≠ 0`, `det H^(4) = 0`, and hence the Hankel rank is exactly `3`.
    thm:fold-gauge-anomaly-hankel-jordan-certificate -/
theorem paper_fold_gauge_anomaly_hankel_jordan_certificate (h : GaugeAnomalyAutocovarianceData) :
    h.hankelDet3Nonzero ∧ h.hankelDet4Zero ∧ h.hankelRankEqThree := by
  refine ⟨?_, hankel4_det_zero h, ?_⟩
  · rw [GaugeAnomalyAutocovarianceData.hankelDet3Nonzero, hankel3_det]
    norm_num
  · rw [GaugeAnomalyAutocovarianceData.hankelRankEqThree]
    have hle : h.hankel4.rank ≤ 3 := hankel4_rank_le_three h
    have hge : 3 ≤ h.hankel4.rank := hankel4_rank_ge_three h
    omega

end GaugeAnomalyAutocovarianceData

end Omega.Folding
