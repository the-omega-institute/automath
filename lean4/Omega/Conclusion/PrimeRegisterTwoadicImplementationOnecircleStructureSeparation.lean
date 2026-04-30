import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-prime-register-twoadic-implementation-onecircle-structure-separation`. -/
theorem paper_conclusion_prime_register_twoadic_implementation_onecircle_structure_separation
    (implementationDim structureCdim : Nat) (hImpl : implementationDim = 2)
    (hStruct : structureCdim = 1) :
    implementationDim = 2 ∧ structureCdim = 1 ∧ structureCdim < implementationDim := by
  subst implementationDim
  subst structureCdim
  norm_num

end Omega.Conclusion
