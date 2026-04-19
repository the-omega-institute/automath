import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- Concrete layerwise bookkeeping for a covering tower with boundary exponents, collar-form
integrals, and a normalized Stokes current. The height of the `n`th level is the base height
raised to the sum of the boundary exponents on that layer. -/
structure CoveringTowerGodelBoundaryNormalizedStokesSystem where
  H0 : ℝ
  H0_pos : 0 < H0
  boundaryDegree : ℕ → ℕ
  boundaryLabel : ∀ n, Fin (boundaryDegree n) → ℕ
  boundaryExponent : ∀ n, Fin (boundaryDegree n) → ℕ
  collarFormIntegral : ∀ n, Fin (boundaryDegree n) → ℝ
  baseBoundaryValue : ℕ → ℝ
  baseCurrentValue : ℕ → ℝ
  baseLayerCompatibility : ∀ n, baseBoundaryValue (n + 1) = baseBoundaryValue n
  baseCurrent_eq_boundary : ∀ n, baseCurrentValue n = baseBoundaryValue n
  collarSum :
    ∀ n, (∑ i : Fin (boundaryDegree n), collarFormIntegral n i) =
      baseBoundaryValue n * H0 ^ (∑ i : Fin (boundaryDegree n), boundaryExponent n i)

def degreeProduct (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℕ :=
  ∑ i : Fin (S.boundaryDegree n), S.boundaryExponent n i

def boundaryHeight (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  S.H0 ^ degreeProduct S n

def boundaryIntegral (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  S.baseBoundaryValue n * boundaryHeight S n

def currentIntegral (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  S.baseCurrentValue n * boundaryHeight S n

def normalizedBoundary (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  boundaryIntegral S n / boundaryHeight S n

def normalizedCurrent (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) : ℝ :=
  currentIntegral S n / boundaryHeight S n

def strictPowerLaw (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) : Prop :=
  ∀ n, boundaryHeight S n = S.H0 ^ degreeProduct S n

def boundaryCostStokesRealization (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) : Prop :=
  ∀ n,
    normalizedBoundary S n =
        (∑ i : Fin (S.boundaryDegree n), S.collarFormIntegral n i) / boundaryHeight S n ∧
      normalizedBoundary S n = normalizedCurrent S n

def inverseLimitCompatibility (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) : Prop :=
  ∀ n,
    normalizedBoundary S (n + 1) = normalizedBoundary S n ∧
      normalizedCurrent S (n + 1) = normalizedCurrent S n

lemma boundaryHeight_pos (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) :
    0 < boundaryHeight S n := by
  unfold boundaryHeight
  exact pow_pos S.H0_pos _

lemma normalizedBoundary_eq_base (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) :
    normalizedBoundary S n = S.baseBoundaryValue n := by
  have hHeight_ne : boundaryHeight S n ≠ 0 := (boundaryHeight_pos S n).ne'
  unfold normalizedBoundary boundaryIntegral
  field_simp [hHeight_ne]

lemma normalizedCurrent_eq_base (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) (n : ℕ) :
    normalizedCurrent S n = S.baseCurrentValue n := by
  have hHeight_ne : boundaryHeight S n ≠ 0 := (boundaryHeight_pos S n).ne'
  unfold normalizedCurrent currentIntegral
  field_simp [hHeight_ne]

/-- Boundary-cost realization, strict power growth, and inverse-limit compatibility for the
normalized Stokes package attached to a covering tower.
    thm:app-covering-tower-godel-boundary-normalized-stokes -/
theorem paper_app_covering_tower_godel_boundary_normalized_stokes
    (S : CoveringTowerGodelBoundaryNormalizedStokesSystem) :
    strictPowerLaw S ∧ boundaryCostStokesRealization S ∧ inverseLimitCompatibility S := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    constructor
    · unfold normalizedBoundary boundaryIntegral boundaryHeight degreeProduct
      rw [S.collarSum n]
    · rw [normalizedBoundary_eq_base, normalizedCurrent_eq_base, S.baseCurrent_eq_boundary]
  · intro n
    constructor
    · rw [normalizedBoundary_eq_base, normalizedBoundary_eq_base, S.baseLayerCompatibility]
    · rw [normalizedCurrent_eq_base, normalizedCurrent_eq_base]
      rw [S.baseCurrent_eq_boundary, S.baseCurrent_eq_boundary, S.baseLayerCompatibility]

end

end Omega.Multiscale
