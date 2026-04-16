import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper-facing seed for the uniqueness of circle dimension under the axioms from
    `thm:cdim-axiomatic-rigidity`. -/
theorem paper_cdim_axiomatic_rigidity_seeds (f : Nat → Nat → Nat)
    (hAdd : ∀ a b c d, f (a + b) (c + d) = f a c + f b d)
    (hNorm : f 1 0 = 1)
    (hFin : ∀ t, f 0 t = 0) :
    ∀ n t, f n t = circleDim n t :=
  paper_circleDim_axiomatic_rigidity f hAdd hNorm hFin

/-- Paper-facing uniqueness theorem for the half circle dimension under additive,
    torsion-vanishing, and `1/2` normalization axioms.
    prop:cdim-plus-axiomatic-uniqueness -/
theorem paper_cdim_plus_axiomatic_uniqueness (f : Nat → Nat → ℚ)
    (hAdd : ∀ a b c d, f (a + b) (c + d) = f a c + f b d)
    (hNorm : f 1 0 = (1 : ℚ) / 2)
    (hFin : ∀ t, f 0 t = 0) :
    ∀ n t, f n t = halfCircleDim n t := by
  intro n t
  have htors : f n t = f n 0 := by
    have h := hAdd n 0 0 t
    simpa [hFin t] using h
  have hfree : ∀ n : Nat, f n 0 = (n : ℚ) / 2 := by
    intro n
    induction n with
    | zero =>
        simpa using hFin 0
    | succ n ih =>
        have h := hAdd n 1 0 0
        calc
          f (n + 1) 0 = f n 0 + f 1 0 := by simpa using h
          _ = (n : ℚ) / 2 + (1 : ℚ) / 2 := by rw [ih, hNorm]
          _ = ((n + 1 : Nat) : ℚ) / 2 := by
            field_simp
            norm_num [Nat.cast_add]
  rw [htors, hfree]
  simp [halfCircleDim, circleDim]

end Omega.CircleDimension
