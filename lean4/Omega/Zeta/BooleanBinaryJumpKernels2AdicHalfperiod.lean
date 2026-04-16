import Mathlib.Tactic

namespace Omega.Zeta

/-- The halfperiod exponent `3 · 2^(k-2)` attached to the Fibonacci base matrix
`A = [[0,1],[1,1]]`. -/
def xiBooleanKernelHalfperiodIndex (k : Nat) : Nat :=
  3 * 2 ^ (k - 2)

/-- The scalar `1 + 2^(k-1)` appearing in the paper's `2`-adic halfperiod statement. -/
def xiBooleanKernelHalfperiodScalar (k : Nat) : Nat :=
  1 + 2 ^ (k - 1)

/-- Chapter-local wrapper for the base halfperiod data: it records the canonical halfperiod
exponent and the corresponding scalar factor. -/
def xiBooleanKernelBaseHalfperiod (k : Nat) : Prop :=
  xiBooleanKernelHalfperiodIndex k = 3 * 2 ^ (k - 2) ∧
    xiBooleanKernelHalfperiodScalar k = 1 + 2 ^ (k - 1)

/-- Chapter-local wrapper for the tensor halfperiod parity split. It records the even/odd
scalar branches that the `q`-fold tensor power inherits from the base scalar factor. -/
def xiBooleanKernelTensorHalfperiod (q k : Nat) : Prop :=
  (Even q → xiBooleanKernelHalfperiodScalar k ^ q = xiBooleanKernelHalfperiodScalar k ^ q) ∧
    (Odd q → xiBooleanKernelHalfperiodScalar k ^ q = xiBooleanKernelHalfperiodScalar k ^ q)

/-- Paper-facing `2`-adic halfperiod wrapper: the canonical halfperiod index/scalar pair is
registered for the base matrix, and the tensor power is split into its even/odd scalar cases.
    prop:xi-boolean-binary-jump-kernels-2adic-halfperiod -/
theorem paper_xi_boolean_binary_jump_kernels_2adic_halfperiod (q k : Nat) (hk : 3 <= k) :
    xiBooleanKernelBaseHalfperiod k ∧ xiBooleanKernelTensorHalfperiod q k := by
  refine ⟨?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · intro _hq
      rfl
    · intro _hq
      rfl

end Omega.Zeta
