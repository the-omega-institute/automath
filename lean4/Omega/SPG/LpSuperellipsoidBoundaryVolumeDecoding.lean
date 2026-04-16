import Mathlib.Tactic

namespace Omega.SPG

/-- The zeroth boundary flux `B₀ = d * Vol(Ω)`. -/
def lpSuperellipsoidBoundaryFlux0 (d : Nat) (volume : ℝ) : ℝ :=
  (d : ℝ) * volume

/-- The `i`-th boundary flux `Bᵢ = aᵢ^p * Vol(Ω)`. -/
def lpSuperellipsoidBoundaryFlux {d : Nat} (p : Nat) (volume : ℝ) (a : Fin d → ℝ)
    (i : Fin d) : ℝ :=
  a i ^ p * volume

/-- Decode the volume from the zeroth boundary flux. -/
noncomputable def lpSuperellipsoidDecodedVolume (d : Nat) (B0 : ℝ) : ℝ :=
  B0 / d

/-- Decode `aᵢ^p` from the flux ratio `d * Bᵢ / B₀`. -/
noncomputable def lpSuperellipsoidDecodedAxisPower (d : Nat) (B0 Bi : ℝ) : ℝ :=
  d * Bi / B0

/-- Paper-facing boundary/volume decoding identity for the diagonal `ℓ_p` superellipsoid model:
    the zeroth flux decodes the volume, each coordinate flux is `aᵢ^p` times that volume, and
    the ratio `d * Bᵢ / B₀` recovers `aᵢ^p`.
    thm:spg-lp-superellipsoid-boundary-volume-decoding -/
theorem paper_spg_lp_superellipsoid_boundary_volume_decoding
    (d p : Nat) (a : Fin d → ℝ) (volume : ℝ)
    (hd : 2 ≤ d) (_hp : 1 < p) (hvol : 0 < volume) :
    lpSuperellipsoidDecodedVolume d (lpSuperellipsoidBoundaryFlux0 d volume) = volume ∧
    (∀ i : Fin d,
      lpSuperellipsoidBoundaryFlux p volume a i =
        a i ^ p * lpSuperellipsoidDecodedVolume d (lpSuperellipsoidBoundaryFlux0 d volume)) ∧
    (∀ i : Fin d,
      lpSuperellipsoidDecodedAxisPower d (lpSuperellipsoidBoundaryFlux0 d volume)
        (lpSuperellipsoidBoundaryFlux p volume a i) = a i ^ p) := by
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdNat)
  have hvol0 : volume ≠ 0 := by linarith
  have hdecode :
      lpSuperellipsoidDecodedVolume d (lpSuperellipsoidBoundaryFlux0 d volume) = volume := by
    unfold lpSuperellipsoidDecodedVolume lpSuperellipsoidBoundaryFlux0
    field_simp [hd0]
  refine ⟨hdecode, ?_, ?_⟩
  · intro i
    rw [hdecode, lpSuperellipsoidBoundaryFlux]
  · intro i
    have hB0 : lpSuperellipsoidBoundaryFlux0 d volume ≠ 0 := by
      unfold lpSuperellipsoidBoundaryFlux0
      exact mul_ne_zero hd0 hvol0
    unfold lpSuperellipsoidDecodedAxisPower lpSuperellipsoidBoundaryFlux lpSuperellipsoidBoundaryFlux0
    field_simp [hB0]

end Omega.SPG
