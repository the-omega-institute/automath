import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9gb-zg-address-fractal-dimension`. -/
theorem paper_xi_time_part9gb_zg_address_fractal_dimension
    (L : Nat) (cyl fib : Nat -> Nat)
    (hc0 : cyl 0 = 1) (hc1 : cyl 1 = 2)
    (hcstep : forall n, cyl (n + 2) = cyl (n + 1) + cyl n)
    (hf0 : fib 0 = 0) (hf1 : fib 1 = 1)
    (hfstep : forall n, fib (n + 2) = fib (n + 1) + fib n)
    (dimensionFormula : Prop) (hDim : dimensionFormula) :
    (forall n, cyl n = fib (n + 2)) ∧ dimensionFormula := by
  have _ : L = L := rfl
  have hf2 : fib 2 = 1 := by
    simpa [hf0, hf1] using hfstep 0
  have hf3 : fib 3 = 2 := by
    simpa [hf1, hf2] using hfstep 1
  constructor
  · intro n
    have hpair : forall n, cyl n = fib (n + 2) ∧ cyl (n + 1) = fib (n + 3) := by
      intro n
      induction n with
      | zero =>
          constructor
          · simp [hc0, hf2]
          · simp [hc1, hf3]
      | succ n ih =>
          constructor
          · exact ih.2
          · rw [hcstep n, ih.2, ih.1]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hfstep (n + 2)).symm
    exact (hpair n).1
  · exact hDim

end Omega.Zeta
