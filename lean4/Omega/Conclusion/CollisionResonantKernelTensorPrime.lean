import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:conclusion-collision-resonant-kernel-tensor-prime`. Since `11` is prime,
any factorization `11 = d1 * d2` forces one factor to be trivial. -/
theorem paper_conclusion_collision_resonant_kernel_tensor_prime {d1 d2 : Nat}
    (hprime : Nat.Prime 11) (hdeg : 11 = d1 * d2) : d1 = 1 ∨ d2 = 1 := by
  have hd1 : d1 = 1 ∨ d1 = 11 := hprime.eq_one_or_self_of_dvd d1 ⟨d2, hdeg⟩
  rcases hd1 with rfl | rfl
  · exact Or.inl rfl
  · have hd2 : d2 = 1 ∨ d2 = 11 :=
      hprime.eq_one_or_self_of_dvd d2 ⟨11, by simpa [Nat.mul_comm] using hdeg⟩
    rcases hd2 with rfl | rfl
    · exact Or.inr rfl
    · exfalso
      norm_num at hdeg

end Omega.Conclusion
