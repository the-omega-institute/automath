import Omega.Conclusion.Period3FiberWalshRankonePrimitives

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-period3-fiber-proper-coordinate-top-parity-blindness`. -/
theorem paper_conclusion_period3_fiber_proper_coordinate_top_parity_blindness {n : ℕ}
    (S : Finset (Fin n)) (hS : S ≠ (Finset.univ : Finset (Fin n))) (w : Omega.Word n) :
    Omega.Conclusion.conclusion_period3_fiber_mobius_walsh_tensorization_conditional S
      (fun u : Omega.Word n => Omega.Core.walshChar (Finset.univ : Finset (Fin n)) u) w =
        0 := by
  classical
  unfold conclusion_period3_fiber_mobius_walsh_tensorization_conditional
  refine Finset.sum_eq_zero ?_
  intro T hT
  rw [conclusion_period3_fiber_mobius_walsh_tensorization_primitive]
  have hTne : T ≠ (Finset.univ : Finset (Fin n)) := by
    intro hTuniv
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ S := by
      simpa [hTuniv] using (Finset.mem_powerset.mp hT)
    apply hS
    ext i
    constructor
    · intro _
      simp
    · intro _
      exact hsub (Finset.mem_univ i)
  rw [Omega.Core.walshBias_expand_basis]
  simp [hTne]

end Omega.Conclusion
