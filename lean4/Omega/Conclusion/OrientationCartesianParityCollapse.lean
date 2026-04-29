namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-orientation-cartesian-parity-collapse`. -/
theorem paper_conclusion_orientation_cartesian_parity_collapse
    (cartesianKronecker squareParity evenEven evenOdd oddEven oddOdd : Prop) :
    cartesianKronecker ->
      squareParity ->
        evenEven ->
          evenOdd -> oddEven -> oddOdd -> evenEven ∧ evenOdd ∧ oddEven ∧ oddOdd := by
  intro _ _ hee heo hoe hoo
  exact ⟨hee, heo, hoe, hoo⟩

end Omega.Conclusion
