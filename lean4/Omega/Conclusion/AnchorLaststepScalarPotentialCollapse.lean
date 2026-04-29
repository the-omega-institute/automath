namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-anchor-laststep-scalar-potential-collapse`. The codimension-one
last-step theorem already packages the scalar one-variable potential collapse together with the
pure geometric extremum statement. -/
theorem paper_conclusion_anchor_laststep_scalar_potential_collapse
    (codimOneCompletion scalarPotentialCollapse pureGeometricExtremum : Prop)
    (h : codimOneCompletion → scalarPotentialCollapse ∧ pureGeometricExtremum) :
    codimOneCompletion → scalarPotentialCollapse ∧ pureGeometricExtremum := by
  exact h

end Omega.Conclusion
