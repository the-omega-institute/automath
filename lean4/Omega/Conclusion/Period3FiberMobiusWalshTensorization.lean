import Omega.Core.WalshFourier

namespace Omega.Conclusion

open scoped BigOperators

/-- The scaled Walsh primitive attached to a Boolean coordinate subset.  The normalization is
left scaled by `2^n`, matching the integer-valued Walsh inversion theorem already available in
`Omega.Core`. -/
def conclusion_period3_fiber_mobius_walsh_tensorization_primitive {n : ℕ}
    (f : Omega.Word n → ℤ) (S : Finset (Fin n)) (w : Omega.Word n) : ℤ :=
  Omega.Core.walshBias f S * Omega.Core.walshChar S w

/-- The coordinate conditional expectation seen through the Walsh-Hoeffding truncation:
only Walsh primitives supported inside `S` are retained. -/
def conclusion_period3_fiber_mobius_walsh_tensorization_conditional {n : ℕ}
    (S : Finset (Fin n)) (f : Omega.Word n → ℤ) (w : Omega.Word n) : ℤ :=
  ∑ T ∈ S.powerset,
    conclusion_period3_fiber_mobius_walsh_tensorization_primitive f T w

/-- The scaled identity operator is the sum of all Walsh primitives. -/
def conclusion_period3_fiber_mobius_walsh_tensorization_identity_scaled {n : ℕ}
    (f : Omega.Word n → ℤ) (w : Omega.Word n) : ℤ :=
  ∑ S : Finset (Fin n),
    conclusion_period3_fiber_mobius_walsh_tensorization_primitive f S w

/-- Paper label: `thm:conclusion-period3-fiber-mobius-walsh-tensorization`.

The Boolean-fiber Walsh primitives tensorize over coordinates: summing the primitive indexed by
`S` over all subsets gives the scaled identity, while truncating to `T ⊆ S` gives the coordinate
conditional expectation `E_S`. -/
theorem paper_conclusion_period3_fiber_mobius_walsh_tensorization {n : ℕ}
    (f : Omega.Word n → ℤ) (w : Omega.Word n) :
    (∑ S : Finset (Fin n),
        conclusion_period3_fiber_mobius_walsh_tensorization_primitive f S w =
      (2 : ℤ) ^ n * f w) ∧
    (∀ S : Finset (Fin n),
      conclusion_period3_fiber_mobius_walsh_tensorization_conditional S f w =
        ∑ T ∈ S.powerset,
          conclusion_period3_fiber_mobius_walsh_tensorization_primitive f T w) ∧
    conclusion_period3_fiber_mobius_walsh_tensorization_identity_scaled f w =
      (2 : ℤ) ^ n * f w := by
  classical
  have hWalsh := Omega.Core.paper_walsh_fourier_inversion_completeness f w
  have hPrimitive :
      ∑ S : Finset (Fin n),
          conclusion_period3_fiber_mobius_walsh_tensorization_primitive f S w =
        (2 : ℤ) ^ n * f w := by
    simpa [conclusion_period3_fiber_mobius_walsh_tensorization_primitive] using hWalsh.symm
  refine ⟨hPrimitive, ?_, ?_⟩
  · intro S
    rfl
  · simpa [conclusion_period3_fiber_mobius_walsh_tensorization_identity_scaled] using hPrimitive

end Omega.Conclusion
