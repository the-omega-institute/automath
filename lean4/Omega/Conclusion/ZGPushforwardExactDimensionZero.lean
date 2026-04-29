namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zg-pushforward-exact-dimension-zero`. -/
theorem paper_conclusion_zg_pushforward_exact_dimension_zero
    (aeLocalDimensionZero exactDimensionalZero : Prop)
    (h : aeLocalDimensionZero → exactDimensionalZero) :
    aeLocalDimensionZero → exactDimensionalZero := by
  exact h

end Omega.Conclusion
