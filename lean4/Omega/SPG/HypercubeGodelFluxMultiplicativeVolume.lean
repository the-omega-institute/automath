import Mathlib.Data.Real.Basic
import Omega.SPG.WeightedDiscreteFluxIdentity

namespace Omega.SPG

open scoped BigOperators

noncomputable section

/-- Coordinatewise multiplicative Gödel code attached to the prime weights `p`. -/
def hypercubeGodelCode {n : ℕ} (p : Fin n → ℕ) (w : Omega.Word n) : Real :=
  ∏ j, if w j then (p j : Real) else 1

/-- Multiplicative zero-layer volume on the `i = 0` side of `S`. -/
def hypercubeGodelZeroLayerVolume {n : ℕ} (i : Fin n) (S : Finset (Omega.Word n))
    (p : Fin n → ℕ) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S), hypercubeGodelCode p w

/-- Multiplicative one-layer volume on the `i = 1` side of `S`, rewritten on the `i = 0` side by
`flipAt`. -/
def hypercubeGodelOneLayerVolume {n : ℕ} (i : Fin n) (S : Finset (Omega.Word n))
    (p : Fin n → ℕ) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ flipAt i w ∈ S),
    hypercubeGodelCode p (flipAt i w)

/-- The multiplicative Gödel flux law is the weighted discrete-flux identity specialized to the
coordinate product code. -/
def hypercubeGodelFluxMultiplicativeVolumeLaw {n : ℕ} (S : Finset (Omega.Word n))
    (p : Fin n → ℕ) : Prop :=
  ∀ i : Fin n,
    (p i : Real) * weightedCutFluxPos i S (fun j => (p j : Real)) -
      weightedCutFluxNeg i S (fun j => (p j : Real)) =
    (p i : Real) * hypercubeGodelZeroLayerVolume i S p - hypercubeGodelOneLayerVolume i S p

/-- Specialize the weighted cut-flux identity to the multiplicative Gödel code.
    prop:fold-hypercube-godel-flux-multiplicative-volume -/
theorem paper_fold_hypercube_godel_flux_multiplicative_volume (S : Finset (Omega.Word n))
    (p : Fin n → ℕ) : hypercubeGodelFluxMultiplicativeVolumeLaw S p := by
  intro i
  simpa [hypercubeGodelCode, hypercubeGodelZeroLayerVolume, hypercubeGodelOneLayerVolume] using
    (paper_fold_hypercube_weighted_discrete_flux_identity (i := i) (S := S)
      (a := fun j => (p j : Real)))

end

end Omega.SPG
