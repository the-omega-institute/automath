import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open AddMonoidAlgebra

/-- Multi-indices in `ℕ^d`, represented as finitely supported functions on `Fin d`. -/
abbrev MultiIndex (d : ℕ) := Fin d →₀ ℕ

/-- Finitely supported coefficient families on `ℕ^d`. This is the multishift polynomial model. -/
abbrev MultishiftPolynomial (d : ℕ) := AddMonoidAlgebra ℤ (MultiIndex d)

/-- The basis vector at multi-index `n`. -/
noncomputable def multishiftBasis {d : ℕ} (n : MultiIndex d) : MultishiftPolynomial d :=
  AddMonoidAlgebra.single n 1

/-- The `i`-th coordinate shift in `ℕ^d`. -/
noncomputable def multishiftCoordinateShift {d : ℕ} (i : Fin d) : MultiIndex d :=
  Finsupp.single i 1

/-- The multishift operator determined by the coefficient family `f`, evaluated on the basis
vector at `n`. -/
noncomputable def multishiftBasisImage {d : ℕ} (f : MultishiftPolynomial d) (n : MultiIndex d) :
    MultishiftPolynomial d :=
  multishiftBasis n * f

/-- Paper label: `thm:conclusion-multishift-commuting-algorithms-polynomial`.
In the finitely supported `ℕ^d` model, the image of the origin basis vector uniquely determines the
whole commuting multishift operator, and pointwise addition/composition become polynomial
addition/Cauchy-product multiplication. -/
theorem paper_conclusion_multishift_commuting_algorithms_polynomial
    (d : ℕ) (f g : MultishiftPolynomial d) :
    (∃! c : MultishiftPolynomial d, multishiftBasisImage c 0 = multishiftBasisImage f 0) ∧
      (∀ i : Fin d, ∀ n : MultiIndex d,
        multishiftBasisImage f (n + multishiftCoordinateShift i) =
          multishiftBasis (multishiftCoordinateShift i) * multishiftBasisImage f n) ∧
      (∀ n : MultiIndex d,
        multishiftBasisImage (f + g) n = multishiftBasisImage f n + multishiftBasisImage g n) ∧
      (∀ n : MultiIndex d,
        multishiftBasisImage (f * g) n = multishiftBasisImage f n * g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨f, ?_, ?_⟩
    · simp [multishiftBasisImage, multishiftBasis]
    · intro c hc
      simpa [multishiftBasisImage, multishiftBasis] using hc
  · intro i n
    calc
      multishiftBasisImage f (n + multishiftCoordinateShift i)
          = multishiftBasis (n + multishiftCoordinateShift i) * f := rfl
      _ = (multishiftBasis n * multishiftBasis (multishiftCoordinateShift i)) * f := by
            simpa [multishiftBasis, multishiftCoordinateShift] using
              congrArg (fun p : MultishiftPolynomial d => p * f)
                (AddMonoidAlgebra.single_mul_single n (multishiftCoordinateShift i) (1 : ℤ) 1).symm
      _ = multishiftBasis (multishiftCoordinateShift i) * multishiftBasisImage f n := by
            rw [multishiftBasisImage]
            ac_rfl
  · intro n
    rw [multishiftBasisImage, multishiftBasisImage, multishiftBasisImage, mul_add]
  · intro n
    rw [multishiftBasisImage, multishiftBasisImage, mul_assoc]

end Omega.Conclusion
