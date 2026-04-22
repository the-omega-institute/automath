import Omega.Conclusion.CyclicZeckendorfSectorCharacterClosedForm

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cyclic-zeckendorf-prime-regular-bias`. At prime modulus, the
trivial character contributes the extra `1`, while every nontrivial character occurs with the
common baseline multiplicity `(L_p - 1) / p`. -/
theorem paper_conclusion_cyclic_zeckendorf_prime_regular_bias (p : ℕ) (hp : p.Prime) :
    let a_p : ℤ := (cyclicZeckendorfLucas p - 1) / p;
    cyclicZeckendorfCharacterMultiplicity p 0 = a_p + 1 ∧
      (∀ k, 0 < k → k < p → cyclicZeckendorfCharacterMultiplicity p k = a_p) := by
  dsimp
  refine ⟨?_, ?_⟩
  · simp [cyclicZeckendorfCharacterMultiplicity, cyclicZeckendorfCharacterClosedForm, hp, hp.ne_zero]
  intro k hk hkp
  have hkne : k ≠ 0 := Nat.ne_of_gt hk
  simp [cyclicZeckendorfCharacterMultiplicity, cyclicZeckendorfCharacterClosedForm, hp, hp.ne_zero,
    hkne]

end Omega.Conclusion
