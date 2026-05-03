namespace Omega.Zeta

/-- Paper label: `thm:xi-time-euler-product-under-zero-mixed-curvature`.
Zero mixed curvature and Euler-product validity are equivalent once both abstract
factorization directions are available. -/
theorem paper_xi_time_euler_product_under_zero_mixed_curvature
    (zeroMixedCurvature eulerProduct : Prop)
    (hforward : zeroMixedCurvature → eulerProduct)
    (hbackward : eulerProduct → zeroMixedCurvature) :
    zeroMixedCurvature ↔ eulerProduct := by
  exact ⟨hforward, hbackward⟩

end Omega.Zeta
