import Omega.Zeta.XiDepthHankelDeterminantVandermondeSquare

namespace Omega.Zeta

/-- Paper label: `cor:xi-gramshift-spectrum-as-phi-image-of-diskpoles`.
Under the disk-pole conjugacy hypothesis, the Gram--shift node spectrum is exactly the
`PhiDelta`-image of the disk poles. -/
theorem paper_xi_gramshift_spectrum_as_phi_image_of_diskpoles (κ : Nat)
    (D : XiFiniteAtomicMomentData κ) (PhiDelta : ℂ → ℂ) (a : Fin κ → ℂ)
    (h_nodes : D.nodes = fun j => PhiDelta (a j)) :
    Set.range D.nodes = Set.range (fun j => PhiDelta (a j)) := by
  simp [h_nodes]

end Omega.Zeta
