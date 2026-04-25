import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-multiplicity-decorated-pinned-datum-rigidity`.
The multiplicity-decorated pinned datum rigidity is the boundary-Cartan projection/inclusion
left-inverse statement from the window-6 splitting. -/
theorem paper_conclusion_window6_multiplicity_decorated_pinned_datum_rigidity :
    Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
      Omega.GU.window6BoundaryCartanInclusion := by
  exact Omega.GU.window6BoundaryCartanProjection_inclusion

end Omega.Conclusion
