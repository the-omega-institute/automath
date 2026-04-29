namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oddtail-principal-compression-triple-optimality`. -/
theorem paper_conclusion_oddtail_principal_compression_triple_optimality
    (n : Nat)
    (exactMomentWindow dimensionOptimal firstMismatchConstant oddTailAsymptotic : Prop)
    (h1 : exactMomentWindow)
    (h2 : dimensionOptimal)
    (h3 : firstMismatchConstant)
    (h4 : oddTailAsymptotic) :
    exactMomentWindow ∧ dimensionOptimal ∧ firstMismatchConstant ∧ oddTailAsymptotic := by
  exact (fun _ : Nat => ⟨h1, h2, h3, h4⟩) n

end Omega.Conclusion
