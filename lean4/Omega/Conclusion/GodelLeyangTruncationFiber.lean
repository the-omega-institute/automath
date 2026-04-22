import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete encoding data for a truncation-by-prefix fiber statement. -/
structure conclusion_godel_leyang_truncation_fiber_data where
  point : Type
  encode : point → ℤ

/-- The residue modulo `2^n` records the first `n` binary digits of the encoded point. -/
def conclusion_godel_leyang_truncation_fiber_prefix
    (D : conclusion_godel_leyang_truncation_fiber_data) (n : ℕ) (x : D.point) : ℤ :=
  D.encode x % ((2 : ℤ) ^ n)

/-- The tail quotient is the encoded point after removing the `n`-digit prefix. -/
def conclusion_godel_leyang_truncation_fiber_tail_quotient
    (D : conclusion_godel_leyang_truncation_fiber_data) (n : ℕ) (x : D.point) : ℤ :=
  D.encode x / ((2 : ℤ) ^ n)

/-- The fiber over the `n`-digit truncation consists of the points with the same prefix. -/
def conclusion_godel_leyang_truncation_fiber_prefix_fiber
    (D : conclusion_godel_leyang_truncation_fiber_data) (n : ℕ) (x : D.point) : Set D.point :=
  {y | conclusion_godel_leyang_truncation_fiber_prefix D n y =
      conclusion_godel_leyang_truncation_fiber_prefix D n x}

/-- The model diameter scales by the `n`th binary contraction factor. -/
def conclusion_godel_leyang_truncation_fiber_diameter
    (_D : conclusion_godel_leyang_truncation_fiber_data) (n : ℕ) : ℚ :=
  1 / (2 ^ n : ℚ)

/-- Paper-facing wrapper: the encoded tail is divisible by the `n`th scale factor, the quotient is
the tail quotient, the fiber is exactly the prefix class, and the model diameter scales by
`2^{-n}`. -/
def conclusion_godel_leyang_truncation_fiber_statement
    (D : conclusion_godel_leyang_truncation_fiber_data) (n : ℕ) (x : D.point) : Prop :=
  ∃ q : ℤ,
    D.encode x - conclusion_godel_leyang_truncation_fiber_prefix D n x = ((2 : ℤ) ^ n) * q ∧
      q = conclusion_godel_leyang_truncation_fiber_tail_quotient D n x ∧
      conclusion_godel_leyang_truncation_fiber_prefix_fiber D n x =
        {y | conclusion_godel_leyang_truncation_fiber_prefix D n y =
            conclusion_godel_leyang_truncation_fiber_prefix D n x} ∧
      conclusion_godel_leyang_truncation_fiber_diameter D n = 1 / (2 ^ n : ℚ)

/-- Paper label: `prop:conclusion-godel-leyang-truncation-fiber`. -/
theorem paper_conclusion_godel_leyang_truncation_fiber
    (D : conclusion_godel_leyang_truncation_fiber_data) (n : ℕ) (x : D.point) :
    conclusion_godel_leyang_truncation_fiber_statement D n x := by
  refine ⟨conclusion_godel_leyang_truncation_fiber_tail_quotient D n x, ?_, rfl, rfl, rfl⟩
  have hdecomp :
      D.encode x = ((2 : ℤ) ^ n) * (D.encode x / ((2 : ℤ) ^ n)) +
        D.encode x % ((2 : ℤ) ^ n) := by
    simpa [mul_comm, add_comm] using (Int.mul_ediv_add_emod (D.encode x) ((2 : ℤ) ^ n)).symm
  exact (sub_eq_iff_eq_add).2 <| by
    simpa [conclusion_godel_leyang_truncation_fiber_prefix,
      conclusion_godel_leyang_truncation_fiber_tail_quotient] using hdecomp

end Omega.Conclusion
