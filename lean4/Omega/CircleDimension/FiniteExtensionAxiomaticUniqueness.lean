import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- In the `(free rank, torsion rank)` bookkeeping model, any additive invariant that vanishes on
    finite groups and is unchanged by finite extensions is a constant multiple of `circleDim`; the
    normalization `F(ℤ)=1` forces equality with `circleDim`.
    prop:cdim-finite-extension-axiomatic-uniqueness -/
theorem paper_cdim_finite_extension_axiomatic_uniqueness (f : Nat → Nat → Nat)
    (hAdd : ∀ a b c d, f (a + b) (c + d) = f a c + f b d)
    (hFin : ∀ t, f 0 t = 0)
    (hExt : ∀ r t, f r t = f r 0) :
    ∃ c : Nat, (∀ r t, f r t = c * circleDim r t) ∧
      (f 1 0 = 1 → ∀ r t, f r t = circleDim r t) := by
  have hfree : ∀ n : Nat, f n 0 = n * f 1 0 := by
    intro n
    induction n with
    | zero =>
        simpa using hFin 0
    | succ n ih =>
        have hstep : f (n + 1) 0 = f n 0 + f 1 0 := by
          simpa using hAdd n 1 0 0
        calc
          f (n + 1) 0 = f n 0 + f 1 0 := hstep
          _ = n * f 1 0 + f 1 0 := by rw [ih]
          _ = (n + 1) * f 1 0 := by rw [Nat.succ_mul]
  have hmain : ∀ r t, f r t = f 1 0 * circleDim r t := by
    intro r t
    calc
      f r t = f r 0 := hExt r t
      _ = r * f 1 0 := hfree r
      _ = f 1 0 * circleDim r t := by simp [circleDim, Nat.mul_comm]
  refine ⟨f 1 0, hmain, ?_⟩
  intro hNorm r t
  calc
    f r t = f 1 0 * circleDim r t := hmain r t
    _ = circleDim r t := by simp [hNorm]

end Omega.CircleDimension
