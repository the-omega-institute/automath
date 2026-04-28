import Mathlib.Tactic

namespace Omega.Zeta

open BigOperators

/-- Concrete finite sector data for the eight boundary characters. -/
structure xi_window6_boundary_eight_sector_central_decomposition_Data where
  sectorAmplitude : Fin 8 -> Complex

/-- Character value of the coordinate character on the finite eight-sector model. -/
def xi_window6_boundary_eight_sector_central_decomposition_characterValue
    (chi sector : Fin 8) : Complex :=
  if chi = sector then 1 else 0

/-- The central idempotent attached to an eight-sector boundary character. -/
def xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent
    (_D : xi_window6_boundary_eight_sector_central_decomposition_Data)
    (chi : Fin 8) : Fin 8 -> Complex :=
  fun sector =>
    xi_window6_boundary_eight_sector_central_decomposition_characterValue chi sector

/-- The action of a central idempotent on a sector vector, in the coordinate model. -/
def xi_window6_boundary_eight_sector_central_decomposition_sectorAction
    (D : xi_window6_boundary_eight_sector_central_decomposition_Data)
    (chi : Fin 8) : Fin 8 -> Complex :=
  fun sector =>
    xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi sector *
      D.sectorAmplitude sector

/-- Idempotence, pairwise orthogonality, sum-to-one, and sector action by character values for
the eight boundary-sector central idempotents. -/
def xi_window6_boundary_eight_sector_central_decomposition_statement
    (D : xi_window6_boundary_eight_sector_central_decomposition_Data) : Prop :=
  (forall chi,
    xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi *
        xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi =
      xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi) /\
    (forall chi chi', Not (chi = chi') ->
      xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi *
          xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi' =
        0) /\
    ((Finset.univ.sum
        (xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D)) =
      1) /\
    (forall chi sector,
      xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent D chi sector =
        xi_window6_boundary_eight_sector_central_decomposition_characterValue chi sector) /\
    (forall chi sector,
      xi_window6_boundary_eight_sector_central_decomposition_sectorAction D chi sector =
        xi_window6_boundary_eight_sector_central_decomposition_characterValue chi sector *
          D.sectorAmplitude sector)

/-- Paper label: `prop:xi-window6-boundary-eight-sector-central-decomposition`. -/
theorem paper_xi_window6_boundary_eight_sector_central_decomposition
    (D : xi_window6_boundary_eight_sector_central_decomposition_Data) :
    xi_window6_boundary_eight_sector_central_decomposition_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro chi
    ext sector
    by_cases h : chi = sector
    · simp [xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent,
        xi_window6_boundary_eight_sector_central_decomposition_characterValue, h]
    · simp [xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent,
        xi_window6_boundary_eight_sector_central_decomposition_characterValue, h]
  · intro chi chi' hne
    ext sector
    by_cases hchi : chi = sector
    · subst chi
      have hchi' : Not (chi' = sector) := by
        intro h
        exact hne h.symm
      simp [xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent,
        xi_window6_boundary_eight_sector_central_decomposition_characterValue, hchi']
    · simp [xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent,
        xi_window6_boundary_eight_sector_central_decomposition_characterValue, hchi]
  · ext sector
    simp [xi_window6_boundary_eight_sector_central_decomposition_centralIdempotent,
      xi_window6_boundary_eight_sector_central_decomposition_characterValue]
  · intro chi sector
    rfl
  · intro chi sector
    rfl

end Omega.Zeta
