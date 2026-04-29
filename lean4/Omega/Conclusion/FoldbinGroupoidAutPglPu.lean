import Mathlib.Tactic

namespace Omega.Conclusion

/-- Multiplicity data for a finite Wedderburn decomposition. -/
structure conclusion_foldbin_groupoid_aut_pgl_pu_data where
  multiplicity : ℕ → ℕ

/-- Symbolic descriptor for one semidirect-product factor in the automorphism decomposition. -/
structure conclusion_foldbin_groupoid_aut_pgl_pu_factor where
  matrixSize : ℕ
  pglCopies : ℕ
  puCopies : ℕ
  symmetricDegree : ℕ
deriving DecidableEq, Repr

/-- The complex-algebra automorphism factor
`PGL_d(C)^{n_d} ⋊ S_{n_d}`, recorded by its finite exponents. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_complexFactor
    (D : conclusion_foldbin_groupoid_aut_pgl_pu_data) (d : ℕ) :
    conclusion_foldbin_groupoid_aut_pgl_pu_factor where
  matrixSize := d
  pglCopies := D.multiplicity d
  puCopies := 0
  symmetricDegree := D.multiplicity d

/-- The star-automorphism factor `PU(d)^{n_d} ⋊ S_{n_d}`, recorded by its finite exponents. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_starFactor
    (D : conclusion_foldbin_groupoid_aut_pgl_pu_data) (d : ℕ) :
    conclusion_foldbin_groupoid_aut_pgl_pu_factor where
  matrixSize := d
  pglCopies := 0
  puCopies := D.multiplicity d
  symmetricDegree := D.multiplicity d

/-- The audited `m = 6` Wedderburn histogram: sizes `2,3,4` with multiplicities `8,4,9`. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity (d : ℕ) : ℕ :=
  if d = 2 then 8 else if d = 3 then 4 else if d = 4 then 9 else 0

/-- The concrete `m = 6` multiplicity datum. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_m6Data :
    conclusion_foldbin_groupoid_aut_pgl_pu_data where
  multiplicity := conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity

/-- Complex automorphism factors for the audited `m = 6` histogram. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_m6ComplexFactors :
    List conclusion_foldbin_groupoid_aut_pgl_pu_factor :=
  [conclusion_foldbin_groupoid_aut_pgl_pu_complexFactor
      conclusion_foldbin_groupoid_aut_pgl_pu_m6Data 2,
    conclusion_foldbin_groupoid_aut_pgl_pu_complexFactor
      conclusion_foldbin_groupoid_aut_pgl_pu_m6Data 3,
    conclusion_foldbin_groupoid_aut_pgl_pu_complexFactor
      conclusion_foldbin_groupoid_aut_pgl_pu_m6Data 4]

/-- Star automorphism factors for the audited `m = 6` histogram. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_m6StarFactors :
    List conclusion_foldbin_groupoid_aut_pgl_pu_factor :=
  [conclusion_foldbin_groupoid_aut_pgl_pu_starFactor
      conclusion_foldbin_groupoid_aut_pgl_pu_m6Data 2,
    conclusion_foldbin_groupoid_aut_pgl_pu_starFactor
      conclusion_foldbin_groupoid_aut_pgl_pu_m6Data 3,
    conclusion_foldbin_groupoid_aut_pgl_pu_starFactor
      conclusion_foldbin_groupoid_aut_pgl_pu_m6Data 4]

/-- Concrete statement for the foldbin groupoid automorphism theorem.  The first two clauses
record the blockwise inner-automorphism plus equal-size permutation decomposition for arbitrary
multiplicity data; the remaining clauses specialize the window-`6` histogram. -/
def conclusion_foldbin_groupoid_aut_pgl_pu_statement
    (D : conclusion_foldbin_groupoid_aut_pgl_pu_data) : Prop :=
  (∀ d,
      conclusion_foldbin_groupoid_aut_pgl_pu_complexFactor D d =
        { matrixSize := d, pglCopies := D.multiplicity d, puCopies := 0,
          symmetricDegree := D.multiplicity d }) ∧
    (∀ d,
      conclusion_foldbin_groupoid_aut_pgl_pu_starFactor D d =
        { matrixSize := d, pglCopies := 0, puCopies := D.multiplicity d,
          symmetricDegree := D.multiplicity d }) ∧
    conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity 2 = 8 ∧
    conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity 3 = 4 ∧
    conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity 4 = 9 ∧
    conclusion_foldbin_groupoid_aut_pgl_pu_m6ComplexFactors =
      [{ matrixSize := 2, pglCopies := 8, puCopies := 0, symmetricDegree := 8 },
        { matrixSize := 3, pglCopies := 4, puCopies := 0, symmetricDegree := 4 },
        { matrixSize := 4, pglCopies := 9, puCopies := 0, symmetricDegree := 9 }] ∧
    conclusion_foldbin_groupoid_aut_pgl_pu_m6StarFactors =
      [{ matrixSize := 2, pglCopies := 0, puCopies := 8, symmetricDegree := 8 },
        { matrixSize := 3, pglCopies := 0, puCopies := 4, symmetricDegree := 4 },
        { matrixSize := 4, pglCopies := 0, puCopies := 9, symmetricDegree := 9 }] ∧
    (8 : ℕ) + 4 + 9 = 21

/-- Paper label: `thm:conclusion-foldbin-groupoid-aut-pgl-pu`. -/
theorem paper_conclusion_foldbin_groupoid_aut_pgl_pu
    (D : conclusion_foldbin_groupoid_aut_pgl_pu_data) :
    conclusion_foldbin_groupoid_aut_pgl_pu_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rfl
  · intro d
    rfl
  · norm_num [conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity]
  · norm_num [conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity]
  · norm_num [conclusion_foldbin_groupoid_aut_pgl_pu_m6Multiplicity]
  · native_decide
  · native_decide
  · omega

end Omega.Conclusion
