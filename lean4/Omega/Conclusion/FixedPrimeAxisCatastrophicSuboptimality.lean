namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fixed-prime-axis-catastrophic-suboptimality`. -/
theorem paper_conclusion_fixed_prime_axis_catastrophic_suboptimality
    (fixedAxisBound exponentialBitLower superSharpDivergence : Prop)
    (h1 : fixedAxisBound → exponentialBitLower)
    (h2 : exponentialBitLower → superSharpDivergence) :
    fixedAxisBound → exponentialBitLower ∧ superSharpDivergence := by
  intro hfixed
  exact ⟨h1 hfixed, h2 (h1 hfixed)⟩

end Omega.Conclusion
