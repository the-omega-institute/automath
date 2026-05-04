import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite Smith valuation profile data.  The profile has finitely many Smith
coordinates and every valuation lies below the recorded prime-power height. -/
structure conclusion_smith_valuation_finite_atomic_certificate_data where
  indexCount : ℕ
  height : ℕ
  valuation : Fin indexCount → ℕ
  valuation_le_height : ∀ i, valuation i ≤ height

/-- A Smith valuation atom at index `i` and prime-power level `k`. -/
def conclusion_smith_valuation_finite_atomic_certificate_atom
    (D : conclusion_smith_valuation_finite_atomic_certificate_data)
    (i : Fin D.indexCount) (k : Fin (D.height + 1)) : Prop :=
  k.val ≤ D.valuation i

/-- Tail count of Smith coordinates whose valuation reaches level `k`. -/
def conclusion_smith_valuation_finite_atomic_certificate_tailCount
    (D : conclusion_smith_valuation_finite_atomic_certificate_data) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin D.indexCount => k ≤ D.valuation i)).card

/-- Exact multiplicity of Smith coordinates with valuation exactly `k`. -/
def conclusion_smith_valuation_finite_atomic_certificate_exactMultiplicity
    (D : conclusion_smith_valuation_finite_atomic_certificate_data) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin D.indexCount => D.valuation i = k)).card

/-- Finite atomic reconstruction statement for a bounded Smith valuation profile. -/
def conclusion_smith_valuation_finite_atomic_certificate_statement
    (D : conclusion_smith_valuation_finite_atomic_certificate_data) : Prop :=
  (∀ i k,
    conclusion_smith_valuation_finite_atomic_certificate_atom D i k ↔
      k.val ≤ D.valuation i) ∧
    ∀ k,
      conclusion_smith_valuation_finite_atomic_certificate_exactMultiplicity D k =
        conclusion_smith_valuation_finite_atomic_certificate_tailCount D k -
          conclusion_smith_valuation_finite_atomic_certificate_tailCount D (k + 1)

lemma conclusion_smith_valuation_finite_atomic_certificate_exactMultiplicity_eq_tail_sub
    (D : conclusion_smith_valuation_finite_atomic_certificate_data) (k : ℕ) :
    conclusion_smith_valuation_finite_atomic_certificate_exactMultiplicity D k =
      conclusion_smith_valuation_finite_atomic_certificate_tailCount D k -
        conclusion_smith_valuation_finite_atomic_certificate_tailCount D (k + 1) := by
  let tailK : Finset (Fin D.indexCount) :=
    Finset.univ.filter (fun i : Fin D.indexCount => k ≤ D.valuation i)
  let tailSucc : Finset (Fin D.indexCount) :=
    Finset.univ.filter (fun i : Fin D.indexCount => k + 1 ≤ D.valuation i)
  have hsubset : tailSucc ⊆ tailK := by
    intro i hi
    simp [tailK, tailSucc] at hi ⊢
    omega
  have hdiff :
      tailK \ tailSucc =
        Finset.univ.filter (fun i : Fin D.indexCount => D.valuation i = k) := by
    ext i
    simp [tailK, tailSucc]
    omega
  calc
    conclusion_smith_valuation_finite_atomic_certificate_exactMultiplicity D k =
        (tailK \ tailSucc).card := by
          rw [hdiff]
          rfl
    _ = tailK.card - (tailSucc ∩ tailK).card := Finset.card_sdiff
    _ = tailK.card - tailSucc.card := by
          rw [Finset.inter_eq_left.mpr hsubset]
    _ =
        conclusion_smith_valuation_finite_atomic_certificate_tailCount D k -
          conclusion_smith_valuation_finite_atomic_certificate_tailCount D (k + 1) := by
          rfl

/-- Paper label: `cor:conclusion-smith-valuation-finite-atomic-certificate`. -/
theorem paper_conclusion_smith_valuation_finite_atomic_certificate
    (D : conclusion_smith_valuation_finite_atomic_certificate_data) :
    conclusion_smith_valuation_finite_atomic_certificate_statement D := by
  refine ⟨?_, ?_⟩
  · intro i k
    rfl
  · intro k
    exact conclusion_smith_valuation_finite_atomic_certificate_exactMultiplicity_eq_tail_sub D k

end Omega.Conclusion
