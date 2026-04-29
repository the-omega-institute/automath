import Mathlib.Tactic

namespace Omega.Conclusion

/-- A finite atomic Big-Witt datum with cycle length `cycleLength` and multiplicity `multiplicity`. -/
structure BigWittAtom where
  weight : ℤ
  cycleLength : ℕ
  multiplicity : ℕ
deriving DecidableEq, Repr

/-- The exact blockwise budget contributed by a single atomic datum. -/
def bigWittAtomBudget (A : BigWittAtom) : ℕ :=
  A.multiplicity * A.cycleLength

/-- The concrete spectral budget of a finite atomic Big-Witt datum. -/
def bigWittSpectralBudget (D : List BigWittAtom) : ℕ :=
  (D.map bigWittAtomBudget).sum

/-- Direct sum is modeled by concatenating the atomic block lists. -/
def bigWittDirectSum (D E : List BigWittAtom) : List BigWittAtom :=
  D ++ E

/-- The atomic tensor rule: one `n`-cycle tensored with one `n'`-cycle splits into
`gcd(n,n')` blocks of length `lcm(n,n')`. -/
def bigWittTensorAtom (A B : BigWittAtom) : BigWittAtom where
  weight := A.weight * B.weight
  cycleLength := Nat.lcm A.cycleLength B.cycleLength
  multiplicity := A.multiplicity * B.multiplicity * Nat.gcd A.cycleLength B.cycleLength

/-- Witt multiplication is modeled by taking all tensor products of atomic blocks. -/
def bigWittWittProduct : List BigWittAtom → List BigWittAtom → List BigWittAtom
  | [], _ => []
  | A :: D, E => E.map (bigWittTensorAtom A) ++ bigWittWittProduct D E

private lemma bigWittSpectralBudget_append (D E : List BigWittAtom) :
    bigWittSpectralBudget (D ++ E) = bigWittSpectralBudget D + bigWittSpectralBudget E := by
  simp [bigWittSpectralBudget, List.map_append, List.sum_append]

private lemma bigWittTensorAtom_budget (A B : BigWittAtom) :
    bigWittAtomBudget (bigWittTensorAtom A B) = bigWittAtomBudget A * bigWittAtomBudget B := by
  simp [bigWittAtomBudget, bigWittTensorAtom, Nat.gcd_mul_lcm, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm]

private lemma bigWittSpectralBudget_map_tensor (A : BigWittAtom) (E : List BigWittAtom) :
    bigWittSpectralBudget (E.map (bigWittTensorAtom A)) =
      bigWittAtomBudget A * bigWittSpectralBudget E := by
  induction E with
  | nil =>
      simp [bigWittSpectralBudget, bigWittAtomBudget]
  | cons B E ih =>
      calc
        bigWittSpectralBudget ((B :: E).map (bigWittTensorAtom A))
            = bigWittAtomBudget (bigWittTensorAtom A B) +
                bigWittSpectralBudget (E.map (bigWittTensorAtom A)) := by
                  simp [bigWittSpectralBudget]
        _ = bigWittAtomBudget A * bigWittAtomBudget B +
              bigWittAtomBudget A * bigWittSpectralBudget E := by
                rw [bigWittTensorAtom_budget, ih]
        _ = bigWittAtomBudget A * (bigWittAtomBudget B + bigWittSpectralBudget E) := by
              rw [Nat.left_distrib]
        _ = bigWittAtomBudget A * bigWittSpectralBudget (B :: E) := by
              simp [bigWittSpectralBudget]

private lemma bigWittSpectralBudget_wittProduct (D E : List BigWittAtom) :
    bigWittSpectralBudget (bigWittWittProduct D E) =
      bigWittSpectralBudget D * bigWittSpectralBudget E := by
  induction D with
  | nil =>
      simp [bigWittWittProduct, bigWittSpectralBudget]
  | cons A D ih =>
      calc
        bigWittSpectralBudget (bigWittWittProduct (A :: D) E)
            = bigWittSpectralBudget (E.map (bigWittTensorAtom A)) +
                bigWittSpectralBudget (bigWittWittProduct D E) := by
                  simp [bigWittWittProduct, bigWittSpectralBudget_append]
        _ = bigWittAtomBudget A * bigWittSpectralBudget E +
              bigWittSpectralBudget D * bigWittSpectralBudget E := by
                rw [bigWittSpectralBudget_map_tensor, ih]
        _ = (bigWittAtomBudget A + bigWittSpectralBudget D) * bigWittSpectralBudget E := by
              rw [Nat.add_mul]
        _ = bigWittSpectralBudget (A :: D) * bigWittSpectralBudget E := by
              simp [bigWittSpectralBudget]

/-- The concrete list model of finite atomic Big-Witt data has exact budget
`∑ m_j n_j`, additive direct sum, and multiplicative Witt product.
    thm:conclusion-bigwitt-exact-spectral-budget -/
theorem paper_conclusion_bigwitt_exact_spectral_budget (D E : List BigWittAtom) :
    bigWittSpectralBudget D = (D.map fun A => A.multiplicity * A.cycleLength).sum ∧
      bigWittSpectralBudget (bigWittDirectSum D E) =
        bigWittSpectralBudget D + bigWittSpectralBudget E ∧
      bigWittSpectralBudget (bigWittWittProduct D E) =
        bigWittSpectralBudget D * bigWittSpectralBudget E := by
  refine ⟨rfl, ?_, bigWittSpectralBudget_wittProduct D E⟩
  simpa [bigWittDirectSum] using bigWittSpectralBudget_append D E

end Omega.Conclusion
