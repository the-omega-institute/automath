import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_xi_order_chain_cauchy_rigidity (t : Nat -> Real) (m0 : Nat) (T : Real)
    (hT : 1 < T)
    (hstep : forall m, m0 <= m ->
      |t (m + 1) - t m| <= Real.exp (-((m + 1 : Real) / 2) * Real.log T) / Real.log T) :
    CauchySeq t := by
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hbase :
      Summable (fun n : ℕ => Real.exp (-((n + 1 : Real) / 2) * Real.log T) / Real.log T) := by
    have hneg : -(Real.log T) / 2 < 0 := by linarith
    convert
      (Real.summable_exp_nat_mul_iff.mpr hneg).mul_left
        (Real.exp (-(Real.log T) / 2) / Real.log T) using 1
    ext n
    have hexp :
        Real.exp (-((n + 1 : Real) / 2) * Real.log T) =
          Real.exp (-(Real.log T) / 2) * Real.exp (n * (-(Real.log T) / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    field_simp [hlogT.ne']
  have htail :
      Summable (fun n : ℕ =>
        Real.exp (-(((m0 + n) + 1 : Real) / 2) * Real.log T) / Real.log T) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (summable_nat_add_iff m0).2 hbase
  have hdistTail :
      Summable (fun n : ℕ => dist (t (m0 + n)) (t (m0 + n + 1))) := by
    refine Summable.of_nonneg_of_le (fun _ => dist_nonneg) ?_ htail
    intro n
    have hm0 : m0 ≤ m0 + n := Nat.le_add_right _ _
    simpa [Real.dist_eq, abs_sub_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hstep (m0 + n) hm0
  have hdist :
      Summable (fun n : ℕ => dist (t n) (t n.succ)) := by
    exact (summable_nat_add_iff m0).1
      (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdistTail)
  exact cauchySeq_of_summable_dist hdist

end Omega.Conclusion
