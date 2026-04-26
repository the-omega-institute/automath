namespace Omega.Conclusion

/-- Equality of output bucket geometry propagates through transfer operators, pressure curves, and
discrete fan invariants.
    thm:conclusion-output-bucket-geometry-preserves-discrete-fan -/
theorem paper_conclusion_output_bucket_geometry_preserves_discrete_fan
    {Aout Operator Pressure Fan : Type} (B B' : Aout → Nat) (L L' : Operator)
    (Λ Λ' : Pressure) (F F' : Fan) (hL : B = B' → L = L') (hΛ : L = L' → Λ = Λ')
    (hF : Λ = Λ' → F = F') (hB : B = B') : L = L' ∧ Λ = Λ' ∧ F = F' := by
  exact ⟨hL hB, hΛ (hL hB), hF (hΛ (hL hB))⟩

end Omega.Conclusion
