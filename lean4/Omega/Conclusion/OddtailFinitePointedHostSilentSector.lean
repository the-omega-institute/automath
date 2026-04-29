import Omega.Conclusion.OddtailMinimalExactCompressorPointedUnitaryRigidity

namespace Omega.Conclusion

/-- A finite pointed host splits into a visible pointed system and a finite silent dimension. -/
structure conclusion_oddtail_finite_pointed_host_silent_sector_FinitePointedHost
    (n : Nat) where
  visible :
    conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n
  silentDimension : Nat

/-- Exact host moments mean exactness of the visible cyclic pointed subsystem. -/
def conclusion_oddtail_finite_pointed_host_silent_sector_ExactMoments
    {n : Nat}
    (H : conclusion_oddtail_finite_pointed_host_silent_sector_FinitePointedHost n) :
    Prop :=
  conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_MinimalExact H.visible

/-- A finite silent sector is represented by its orthogonal complement dimension. -/
structure conclusion_oddtail_finite_pointed_host_silent_sector_SilentSector
    {n : Nat}
    (H : conclusion_oddtail_finite_pointed_host_silent_sector_FinitePointedHost n) where
  dimension : Nat

/-- The visible component is canonical and the chosen complement records all silent dimensions. -/
def conclusion_oddtail_finite_pointed_host_silent_sector_OrthogonalSilentDecomposition
    {n : Nat}
    (H : conclusion_oddtail_finite_pointed_host_silent_sector_FinitePointedHost n)
    (S : conclusion_oddtail_finite_pointed_host_silent_sector_SilentSector H) :
    Prop :=
  S.dimension = H.silentDimension ∧
    conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedUnitaryEquivalent
      H.visible
      (conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_canonicalCompressor
        n)

/-- `prop:conclusion-oddtail-finite-pointed-host-silent-sector`. -/
theorem paper_conclusion_oddtail_finite_pointed_host_silent_sector
    (n : Nat)
    (H : conclusion_oddtail_finite_pointed_host_silent_sector_FinitePointedHost n)
    (hH : conclusion_oddtail_finite_pointed_host_silent_sector_ExactMoments H) :
    ∃ S, conclusion_oddtail_finite_pointed_host_silent_sector_OrthogonalSilentDecomposition
      H S := by
  refine ⟨⟨H.silentDimension⟩, ?_⟩
  constructor
  · rfl
  · exact
      paper_conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity
        n H.visible hH

end Omega.Conclusion
