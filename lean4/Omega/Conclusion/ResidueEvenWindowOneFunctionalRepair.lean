import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-residue-even-window-one-functional-repair`. -/
theorem paper_conclusion_residue_even_window_one_functional_repair {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (b0 chi target : V) (Lambda : V →ₗ[K] K)
    (hLambda : Lambda chi ≠ 0) :
    ∃! b : V, (∃ c : K, b = b0 + c • chi) ∧ Lambda b = Lambda target := by
  let c : K := (Lambda target - Lambda b0) / Lambda chi
  refine ⟨b0 + c • chi, ?_, ?_⟩
  · constructor
    · exact ⟨c, rfl⟩
    · simp [c, map_add, map_smul, hLambda]
  · intro b hb
    rcases hb.1 with ⟨d, rfl⟩
    have hline : Lambda b0 + d * Lambda chi = Lambda target := by
      simpa [map_add, map_smul] using hb.2
    have hd_mul : d * Lambda chi = Lambda target - Lambda b0 := by
      calc
        d * Lambda chi = (Lambda b0 + d * Lambda chi) - Lambda b0 := by ring
        _ = Lambda target - Lambda b0 := by rw [hline]
    have hc_mul : c * Lambda chi = Lambda target - Lambda b0 := by
      simp [c, hLambda]
    have hd : d = c := by
      have hzero : (d - c) * Lambda chi = 0 := by
        rw [sub_mul, hd_mul, hc_mul, sub_self]
      have hdc : d - c = 0 := (mul_eq_zero.mp hzero).resolve_right hLambda
      exact sub_eq_zero.mp hdc
    simp [hd]

end Omega.Conclusion
