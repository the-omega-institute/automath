import Mathlib.Tactic
import Omega.GU.BoundaryDelta34TripleIdentity
import Omega.GU.BoundaryTowerMinimalResonanceTripleSM
import Omega.GU.Window6ChiralityAnchorMinimal

namespace Omega.GU

open BoundaryTowerMinimalResonanceTripleSMData

/-- Wrapper combining the window-6 chirality anchor, the `δ = 34` boundary identity, and the
minimal-resonance triple package: once the boundary triple is the Standard-Model triple, the
window-8 boundary slot of size `8` is forced and carries the unavoidable color-layer dimension.
    cor:m11-intrinsic-chirality-forces-color-layer -/
theorem paper_m11_intrinsic_chirality_forces_color_layer
    (C : Omega.GU.Window6ChiralityAnchorMinimalData)
    (R : Omega.GU.BoundaryTowerMinimalResonanceTripleSMData) :
    R.boundaryTriple = (1, 3, 8) →
      C.minimal_window ∧
      C.unique_boundary_parity ∧
      Nat.fib 9 = 34 ∧
      Nat.fib 6 = 8 ∧
      R.uniqueIsomorphismClass ∧
      R.isStandardModelLieAlgebra := by
  intro hTriple
  rcases paper_window6_chirality_anchor_minimal C with ⟨hMinimal, hParity⟩
  have hDelta := paper_bdry_delta34_triple_identity
  rcases paper_bdry_tower_minimal_resonance_triple_sm R hTriple with ⟨hClass, hSM⟩
  have hSig := paper_gu_sm_signature_union
  exact ⟨hMinimal, hParity, hDelta.1, hSig.2.2.1.symm, hClass, hSM⟩

end Omega.GU
