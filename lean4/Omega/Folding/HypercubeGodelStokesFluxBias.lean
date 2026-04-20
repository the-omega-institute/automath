import Omega.SPG.BoundaryL1BiasMonotone

namespace Omega.Folding

noncomputable section

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev GodelFluxHypercubeVertex (n : ℕ) := Fin n → Bool

/-- The involution that flips the `i`-th bit of a hypercube vertex. -/
abbrev hypercubeBitFlip {n : ℕ} (i : Fin n)
    (ω : GodelFluxHypercubeVertex n) : GodelFluxHypercubeVertex n :=
  Omega.SPG.flipAt i ω

/-- Outward boundary edges in the `0 -> 1` direction across coordinate `i`. -/
def hypercubeOutwardZeroBoundaryCount {n : ℕ} (i : Fin n)
    (S : Finset (GodelFluxHypercubeVertex n)) : ℕ :=
  (Finset.univ.filter
    (fun ω : GodelFluxHypercubeVertex n => ω i = false ∧ ω ∈ S ∧ hypercubeBitFlip i ω ∉ S)).card

/-- Outward boundary edges in the `1 -> 0` direction across coordinate `i`. -/
def hypercubeOutwardOneBoundaryCount {n : ℕ} (i : Fin n)
    (S : Finset (GodelFluxHypercubeVertex n)) : ℕ :=
  (Finset.univ.filter
    (fun ω : GodelFluxHypercubeVertex n => ω i = true ∧ ω ∈ S ∧ hypercubeBitFlip i ω ∉ S)).card

/-- Signed `0`-minus-`1` volume bias along coordinate `i`. -/
abbrev hypercubeVolumeBias {n : ℕ} (i : Fin n) (S : Finset (GodelFluxHypercubeVertex n)) : ℤ :=
  Omega.SPG.volumeBias i S

/-- Total number of unoriented boundary edges across coordinate `i`. -/
def hypercubeBoundaryCount {n : ℕ} (i : Fin n) (S : Finset (GodelFluxHypercubeVertex n)) : ℕ :=
  hypercubeOutwardZeroBoundaryCount i S + hypercubeOutwardOneBoundaryCount i S

/-- Paper label: `prop:fold-hypercube-godel-stokes-flux-bias`. Pairing the internal `i`-edges by
the bit-flip involution leaves only the outward boundary edges, so the signed flux is exactly the
`0`-minus-`1` bias on coordinate `i`. Consequently the unoriented boundary count dominates the
absolute bias. -/
theorem paper_fold_hypercube_godel_stokes_flux_bias {n : ℕ} (i : Fin n)
    (S : Finset (GodelFluxHypercubeVertex n)) :
    (((hypercubeOutwardZeroBoundaryCount i S : ℤ) - hypercubeOutwardOneBoundaryCount i S : ℤ) =
        hypercubeVolumeBias i S) ∧
      Int.natAbs (hypercubeVolumeBias i S) ≤ hypercubeBoundaryCount i S := by
  have hflip_boundary :
      (Finset.univ.filter
        (fun ω : GodelFluxHypercubeVertex n => ω i = false ∧ ω ∉ S ∧ Omega.SPG.flipAt i ω ∈ S)).card =
        hypercubeOutwardOneBoundaryCount i S := by
    simpa [hypercubeOutwardOneBoundaryCount, hypercubeBitFlip] using Omega.SPG.flipAt_bop_card_eq i S
  refine ⟨?_, ?_⟩
  · have hcut :
        Omega.SPG.cutFlux i S =
          (((hypercubeOutwardZeroBoundaryCount i S : ℤ) - hypercubeOutwardOneBoundaryCount i S : ℤ)) := by
      unfold hypercubeOutwardZeroBoundaryCount hypercubeBitFlip
      rw [Omega.SPG.cutFlux, hflip_boundary]
    calc
      (((hypercubeOutwardZeroBoundaryCount i S : ℤ) - hypercubeOutwardOneBoundaryCount i S : ℤ))
          = Omega.SPG.cutFlux i S := hcut.symm
      _ = hypercubeVolumeBias i S := by
        simpa [hypercubeVolumeBias] using Omega.SPG.cutFlux_eq_volumeBias i S
  · simpa [hypercubeVolumeBias, hypercubeBoundaryCount, hypercubeOutwardZeroBoundaryCount,
      hypercubeOutwardOneBoundaryCount, hypercubeBitFlip, hflip_boundary] using
      (Omega.SPG.paper_fold_hypercube_boundary_l1_bias_monotone i S).1

end

end Omega.Folding
