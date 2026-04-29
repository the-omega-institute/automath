import Omega.Conclusion.Period3FiberMobiusWalshTensorization

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-period3-fiber-walsh-rankone-primitives`. -/
theorem paper_conclusion_period3_fiber_walsh_rankone_primitives {n : ℕ}
    (f : Omega.Word n → ℤ) (S : Finset (Fin n)) (w : Omega.Word n) :
    Omega.Conclusion.conclusion_period3_fiber_mobius_walsh_tensorization_primitive f S w =
        Omega.Core.walshBias f S * Omega.Core.walshChar S w ∧
      (∀ T : Finset (Fin n),
        Omega.Core.walshBias (fun u : Omega.Word n => Omega.Core.walshChar T u) S =
          if S = T then (2 : ℤ) ^ n else 0) := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro T
    exact Omega.Core.walshBias_expand_basis S T

end Omega.Conclusion
