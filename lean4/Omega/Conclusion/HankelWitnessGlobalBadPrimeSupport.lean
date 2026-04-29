namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hankel-witness-global-bad-prime-support`. -/
theorem paper_conclusion_hankel_witness_global_bad_prime_support
    (detFactorization valuationIdentity badPrimeSupportContained : Prop)
    (hdet : detFactorization)
    (hval : detFactorization → valuationIdentity)
    (hsupport : valuationIdentity → badPrimeSupportContained) :
    valuationIdentity ∧ badPrimeSupportContained := by
  exact ⟨hval hdet, hsupport (hval hdet)⟩

end Omega.Conclusion
