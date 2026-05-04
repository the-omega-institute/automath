import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-finite-prime-no-faithful-two-circle-splitting`. -/
theorem paper_conclusion_finite_prime_no_faithful_two_circle_splitting
    (faithfulTwoCircleSplitting : Prop) (honeCircleBarrier : Not faithfulTwoCircleSplitting) :
    Not faithfulTwoCircleSplitting := by
  exact honeCircleBarrier

end Omega.Conclusion
