import Omega.Zeta.RecursiveZeroShadowingExplicit

namespace Omega.Zeta

/-- Local certification package extracted from the recursive zero-shadowing theorem.
    cor:xi-rs-local-zero-certification -/
theorem paper_xi_rs_local_zero_certification
    (Z : Real -> Real) (tau r eps mu : Real)
    (hr : 0 < r) (hmu : 0 < mu)
    (hcont : ContinuousOn Z (xiShadowWindow tau r))
    (hmono : StrictMonoOn Z (xiShadowWindow tau r))
    (hleft : Z (tau - r) <= 0) (hright : 0 <= Z (tau + r))
    (htau : |Z tau| <= eps)
    (hslope : forall x, x ∈ xiShadowWindow tau r -> mu * |x - tau| <= |Z x - Z tau|) :
    ∃! gamma, gamma ∈ xiShadowWindow tau r ∧ Z gamma = 0 ∧ |gamma - tau| <= eps / mu := by
  rcases
      paper_xi_recursive_zero_shadowing_explicit Z tau r eps mu hr hmu hcont hmono hleft hright
        htau hslope with
    ⟨hzero, hbound, _⟩
  rcases hzero with ⟨gamma, hgamma, huniq⟩
  refine ⟨gamma, ⟨hgamma.1, hgamma.2, hbound gamma hgamma.1 hgamma.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, hy.2.1⟩

end Omega.Zeta
