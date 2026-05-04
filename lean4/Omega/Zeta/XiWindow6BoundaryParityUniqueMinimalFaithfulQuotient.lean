import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-dimensional data for the window-6 boundary-parity quotient.  The anomaly
signature space has dimension `21`, the boundary parity subspace has dimension `3`, and the
faithful quotient map separates the boundary coordinates inside a target of dimension
`targetDim`. -/
structure xi_window6_boundary_parity_unique_minimal_faithful_quotient_Data where
  xi_window6_boundary_parity_unique_minimal_faithful_quotient_targetDim : ℕ
  xi_window6_boundary_parity_unique_minimal_faithful_quotient_kernelDim : ℕ
  xi_window6_boundary_parity_unique_minimal_faithful_quotient_boundaryToTarget :
    Fin 3 →
      Fin xi_window6_boundary_parity_unique_minimal_faithful_quotient_targetDim
  xi_window6_boundary_parity_unique_minimal_faithful_quotient_boundaryToTarget_injective :
    Function.Injective
      xi_window6_boundary_parity_unique_minimal_faithful_quotient_boundaryToTarget
  xi_window6_boundary_parity_unique_minimal_faithful_quotient_rankNullity :
    xi_window6_boundary_parity_unique_minimal_faithful_quotient_kernelDim +
      xi_window6_boundary_parity_unique_minimal_faithful_quotient_targetDim = 21

namespace xi_window6_boundary_parity_unique_minimal_faithful_quotient_Data

/-- The audited anomaly signature space. -/
abbrev xi_window6_boundary_parity_unique_minimal_faithful_quotient_anomalySignatureSpace
    (_D : xi_window6_boundary_parity_unique_minimal_faithful_quotient_Data) :=
  Fin 21

/-- The boundary-parity subspace whose faithful image forces three visible coordinates. -/
abbrev xi_window6_boundary_parity_unique_minimal_faithful_quotient_boundaryParitySubspace
    (_D : xi_window6_boundary_parity_unique_minimal_faithful_quotient_Data) :=
  Fin 3

end xi_window6_boundary_parity_unique_minimal_faithful_quotient_Data

/-- Paper label:
`cor:xi-window6-boundary-parity-unique-minimal-faithful-quotient`. -/
theorem paper_xi_window6_boundary_parity_unique_minimal_faithful_quotient
    (D : xi_window6_boundary_parity_unique_minimal_faithful_quotient_Data) :
    3 ≤
        D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_targetDim ∧
      (D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_targetDim = 3 →
        D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_kernelDim = 18) := by
  refine ⟨?_, ?_⟩
  · have hcard :
        Fintype.card (Fin 3) ≤
          Fintype.card
            (Fin D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_targetDim) :=
      Fintype.card_le_of_injective
        D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_boundaryToTarget
        D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_boundaryToTarget_injective
    simpa using hcard
  · intro htarget
    have hrank :=
      D.xi_window6_boundary_parity_unique_minimal_faithful_quotient_rankNullity
    omega

end Omega.Zeta
