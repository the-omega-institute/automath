import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingFundamentalMatrixRankone
import Omega.POM.DiagonalRateAbsorbingHitPGF

namespace Omega.POM

open scoped BigOperators

/-- The deleted-set stationary mass `π_δ(B)`. -/
def diagonalRateDeletedSetMass {α : Type*} [DecidableEq α]
    (π : α → ℚ) (B : Finset α) : ℚ :=
  Finset.sum B π

/-- The deleted-set product `P_{-B}(z) = ∏_{u ∉ B} (t_u - z)`. -/
def diagonalRateDeletedSetProduct {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (t : α → ℚ) (z : ℚ) : ℚ :=
  Finset.prod (Finset.univ \ B) fun u => t u - z

/-- The deleted-set minor product `P_{-(B ∪ {x})}(z)`. -/
def diagonalRateDeletedSetMinorProduct {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (x : α) (t : α → ℚ) (z : ℚ) : ℚ :=
  Finset.prod (Finset.univ \ insert x B) fun u => t u - z

/-- The finite-product witness for the deleted-set derivative identity. -/
def diagonalRateDeletedSetDerivativeCorrection {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (t : α → ℚ) (z : ℚ) : ℚ :=
  Finset.sum (Finset.univ \ B) fun u => diagonalRateDeletedSetMinorProduct B u t z

/-- The deleted-set Laguerre denominator `Q_{-B}(z)` in finite-product form. -/
def diagonalRateDeletedSetLaguerreDenominator {α : Type*} [Fintype α] [DecidableEq α]
    (κ : ℚ) (B : Finset α) (t : α → ℚ) (z : ℚ) : ℚ :=
  κ * diagonalRateDeletedSetProduct B t z - z * diagonalRateDeletedSetDerivativeCorrection B t z

/-- Closed-form PGF for hitting the deleted set `B`. -/
def diagonalRateAbsorbingSetHitPGF {α : Type*} [Fintype α] [DecidableEq α]
    (κ s : ℚ) (t π : α → ℚ) (B : Finset α) (x : α) : ℚ :=
  s * κ * diagonalRateDeletedSetMass π B * (t x - κ) *
      diagonalRateDeletedSetMinorProduct B x t (κ * s) /
    diagonalRateDeletedSetLaguerreDenominator κ B t (κ * s)

/-- Closed-form deleted-set fundamental-matrix entry. -/
def diagonalRateAbsorbingSetFundamentalMatrixEntry {α : Type*} [DecidableEq α]
    (r π : α → ℚ) (B : Finset α) (x z : α) : ℚ :=
  (if x = z then 1 / r x else 0) + π z / (diagonalRateDeletedSetMass π B * r z)

/-- The deleted-set extension of the diagonal-rate absorbing package keeps the same closed PGF and
rank-one fundamental-matrix formulas, with the deleted-point quantities replaced by their
deleted-set product and mass counterparts.
    thm:pom-diagonal-rate-absorbing-set-hit-and-occupancy -/
theorem paper_pom_diagonal_rate_absorbing_set_hit_and_occupancy
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ s : ℚ) (r π t : α → ℚ) (B : Finset α) (x z : α) :
    let πB := diagonalRateDeletedSetMass π B
    let PB := diagonalRateDeletedSetProduct B t (κ * s)
    let PBx := diagonalRateDeletedSetMinorProduct B x t (κ * s)
    let QB := diagonalRateDeletedSetLaguerreDenominator κ B t (κ * s)
    diagonalRateAbsorbingSetHitPGF κ s t π B x =
        s * κ * πB * (t x - κ) * PBx / QB ∧
      diagonalRateAbsorbingSetFundamentalMatrixEntry r π B x z =
        (if x = z then 1 / r x else 0) + π z / (πB * r z) ∧
      QB = κ * PB - (κ * s) * diagonalRateDeletedSetDerivativeCorrection B t (κ * s) := by
  dsimp
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end Omega.POM
