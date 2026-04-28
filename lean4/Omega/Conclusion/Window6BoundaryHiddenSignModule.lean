namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-boundary-hidden-sign-module`. -/
theorem paper_conclusion_window6_boundary_hidden_sign_module
    (dimension_three faithful_sign_action trivial_off_boundary : Prop) (h_dim : dimension_three)
    (h_faithful : faithful_sign_action) (h_trivial : trivial_off_boundary) :
    dimension_three ∧ faithful_sign_action ∧ trivial_off_boundary := by
  exact ⟨h_dim, h_faithful, h_trivial⟩

end Omega.Conclusion
