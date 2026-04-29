import Omega.Conclusion.PrimeIntegerizationSuperlinearBitlength

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-godel-sideinfo-superlinear-overhead`. -/
theorem paper_conclusion_godel_sideinfo_superlinear_overhead
    (linearSideInfo superlinearOverhead : Prop) (hSide : linearSideInfo)
    (hGodel : Omega.Conclusion.conclusion_prime_integerization_superlinear_bitlength_statement)
    (hCombine :
      linearSideInfo →
        Omega.Conclusion.conclusion_prime_integerization_superlinear_bitlength_statement →
          superlinearOverhead) :
    superlinearOverhead := by
  exact hCombine hSide hGodel

end Omega.Conclusion
