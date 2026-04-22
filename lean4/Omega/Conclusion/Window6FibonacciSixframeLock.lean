import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-fibonacci-sixframe-lock`. -/
theorem paper_conclusion_window6_fibonacci_sixframe_lock :
    3 = Nat.fib 4 ∧ 5 = Nat.fib 5 ∧ 8 = Nat.fib 6 ∧ 13 = Nat.fib 7 ∧ 21 = Nat.fib 8 ∧
      34 = Nat.fib 9 := by
  rcases godelLift_maxfiber_fib_chain with ⟨h4, h5, h6, h7, h8, h9, _⟩
  exact ⟨h4, h5, h6, h7, h8, h9⟩

end Omega.Conclusion
