namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-xi-natural-boundary-no-finite-recursive-certificate`. -/
theorem paper_conclusion_xi_natural_boundary_no_finite_recursive_certificate
    (RH dense naturalBoundary noFiniteRecursiveCertificate : Prop)
    (hBoundary : RH → dense → naturalBoundary)
    (hNoFinite : naturalBoundary → noFiniteRecursiveCertificate) (hRH : RH) (hDense : dense) :
    naturalBoundary ∧ noFiniteRecursiveCertificate := by
  have hnaturalBoundary : naturalBoundary := hBoundary hRH hDense
  exact ⟨hnaturalBoundary, hNoFinite hnaturalBoundary⟩

end Omega.Conclusion
