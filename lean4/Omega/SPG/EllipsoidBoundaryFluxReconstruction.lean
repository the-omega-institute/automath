import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing algebraic reconstruction of the volume and shape matrix from boundary fluxes.
    thm:spg-ellipsoid-boundary-flux-reconstruction -/
theorem paper_spg_ellipsoid_boundary_flux_reconstruction (d : Nat) (hd : 0 < d)
    (volume B0 : ℝ) (B Q : Fin d → Fin d → ℝ) (hB0 : B0 = (d : ℝ) * volume)
    (hB0_ne : B0 ≠ 0) (hB : ∀ i j, B i j = volume * Q i j) :
    volume = B0 / d ∧ ∀ i j, Q i j = ((d : ℝ) / B0) * B i j := by
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hvol_ne : volume ≠ 0 := by
    intro hvol
    apply hB0_ne
    rw [hB0, hvol]
    simp
  have hvolume : volume = B0 / d := by
    rw [hB0]
    field_simp [hd_ne]
  refine ⟨hvolume, ?_⟩
  intro i j
  rw [hB i j, hB0]
  field_simp [hd_ne, hvol_ne]

end Omega.SPG
