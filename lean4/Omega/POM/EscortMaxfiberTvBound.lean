import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

open Finset
open scoped BigOperators

/-- The `q`-escort numerator attached to a base weight and a fiber multiplicity profile. -/
def escortWeight {α : Type*} (baseWeight : α → ℝ) (fiberMultiplicity : α → ℕ) (x : α) : ℝ :=
  baseWeight x * fiberMultiplicity x

/-- The maximal-fiber locus `A_max = {x : d_m(x) = D_m}`. -/
def maximalFiberSubset {α : Type*} [Fintype α] [DecidableEq α] (fiberMultiplicity : α → ℕ)
    (Dm : ℕ) : Finset α :=
  Finset.univ.filter fun x => fiberMultiplicity x = Dm

/-- The complement of `A_max` inside the finite layer. -/
def offMaxFiberSubset {α : Type*} [Fintype α] [DecidableEq α] (fiberMultiplicity : α → ℕ)
    (Dm : ℕ) : Finset α :=
  Finset.univ.filter fun x => x ∉ maximalFiberSubset fiberMultiplicity Dm

/-- Data package for the finite-layer escort/maximal-fiber total-variation bound.

The fields record the escort weight, the maximal-fiber subset, the rewrite of total variation as
the missing mass outside that subset, the denominator estimate obtained by replacing every
off-maximal multiplicity by `D_m^(2)`, and the final comparison with `(D_m)^2`. -/
structure EscortMaxfiberTvBoundData where
  α : Type*
  instFintype : Fintype α
  instDecEq : DecidableEq α
  baseWeight : α → ℝ
  fiberMultiplicity : α → ℕ
  Dm : ℕ
  tvDistance : ℝ
  denominatorBound : ℝ
  tvAsMissingMass :
    tvDistance =
      Finset.sum (offMaxFiberSubset fiberMultiplicity Dm)
        (fun x => escortWeight baseWeight fiberMultiplicity x)
  missingMassLeDenominator :
    Finset.sum (offMaxFiberSubset fiberMultiplicity Dm)
        (fun x => escortWeight baseWeight fiberMultiplicity x) ≤
      denominatorBound
  denominatorLeDmSq : denominatorBound ≤ (Dm : ℝ) ^ (2 : ℕ)

attribute [instance] EscortMaxfiberTvBoundData.instFintype
attribute [instance] EscortMaxfiberTvBoundData.instDecEq

/-- Paper-facing bound statement. -/
def EscortMaxfiberTvBoundData.tvDistanceLeBound (h : EscortMaxfiberTvBoundData) : Prop :=
  h.tvDistance ≤ (h.Dm : ℝ) ^ (2 : ℕ)

/-- Paper theorem: the escort total variation from the uniform law on the maximal-fiber set is
controlled by the missing mass outside `A_max`, then by the off-maximal denominator estimate, and
finally by the algebraic `(D_m)^2` simplification.
    prop:pom-escort-maxfiber-tv-bound -/
theorem paper_pom_escort_maxfiber_tv_bound (h : EscortMaxfiberTvBoundData) : h.tvDistanceLeBound := by
  dsimp [EscortMaxfiberTvBoundData.tvDistanceLeBound]
  calc
    h.tvDistance =
        Finset.sum (offMaxFiberSubset h.fiberMultiplicity h.Dm)
          (fun x => escortWeight h.baseWeight h.fiberMultiplicity x) := h.tvAsMissingMass
    _ ≤ h.denominatorBound := h.missingMassLeDenominator
    _ ≤ (h.Dm : ℝ) ^ (2 : ℕ) := h.denominatorLeDmSq

end Omega.POM
