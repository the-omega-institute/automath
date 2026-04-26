import Mathlib.Tactic
import Omega.Conclusion.SmithLocalZetaPoleResidueHeadTriple

namespace Omega.Conclusion

open Omega.Zeta

/-- The local Smith spectrum `(2,1,0)` used in the residue-blindness comparison. -/
def conclusion_smith_local_residue_classification_blindness_spectrum210 : Fin 3 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨_, _⟩ => 0

/-- The local Smith spectrum `(1,1,1)` used in the residue-blindness comparison. -/
def conclusion_smith_local_residue_classification_blindness_spectrum111 : Fin 3 → ℕ :=
  fun _ => 1

/-- Paper label: `prop:conclusion-smith-local-residue-classification-blindness`.
The spectra `(2,1,0)` and `(1,1,1)` have the same total `p`-mass, hence the same residue, but
their maximal local height and first platform length differ. -/
theorem paper_conclusion_smith_local_residue_classification_blindness (p : ℕ) :
    conclusion_smith_local_zeta_pole_residue_head_triple_residue p
        conclusion_smith_local_residue_classification_blindness_spectrum210 =
      conclusion_smith_local_zeta_pole_residue_head_triple_residue p
        conclusion_smith_local_residue_classification_blindness_spectrum111 ∧
    conclusion_smith_local_zeta_pole_residue_head_triple_head
        conclusion_smith_local_residue_classification_blindness_spectrum210 = 2 ∧
    conclusion_smith_local_zeta_pole_residue_head_triple_head
        conclusion_smith_local_residue_classification_blindness_spectrum111 = 1 ∧
    smithPrefixValue conclusion_smith_local_residue_classification_blindness_spectrum210 1 = 2 ∧
    smithPrefixValue conclusion_smith_local_residue_classification_blindness_spectrum111 1 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_smith_local_zeta_pole_residue_head_triple_residue,
      conclusion_smith_local_residue_classification_blindness_spectrum210,
      conclusion_smith_local_residue_classification_blindness_spectrum111, Fin.sum_univ_three]
  · unfold conclusion_smith_local_zeta_pole_residue_head_triple_head smithPrefixTop
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro i hi
      fin_cases i <;> decide
    · have hzero :
          conclusion_smith_local_residue_classification_blindness_spectrum210 (0 : Fin 3) ≤
            Finset.univ.sup conclusion_smith_local_residue_classification_blindness_spectrum210 :=
          Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
            (f := fun i : Fin 3 => conclusion_smith_local_residue_classification_blindness_spectrum210 i)
            (by decide : (0 : Fin 3) ∈ Finset.univ)
      simpa [conclusion_smith_local_residue_classification_blindness_spectrum210] using hzero
  · unfold conclusion_smith_local_zeta_pole_residue_head_triple_head smithPrefixTop
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro i hi
      fin_cases i <;> decide
    · have hzero :
          conclusion_smith_local_residue_classification_blindness_spectrum111 (0 : Fin 3) ≤
            Finset.univ.sup conclusion_smith_local_residue_classification_blindness_spectrum111 :=
          Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
            (f := fun i : Fin 3 => conclusion_smith_local_residue_classification_blindness_spectrum111 i)
            (by decide : (0 : Fin 3) ∈ Finset.univ)
      simp [conclusion_smith_local_residue_classification_blindness_spectrum111] at hzero ⊢
  · simp [smithPrefixValue, conclusion_smith_local_residue_classification_blindness_spectrum210,
      Fin.sum_univ_three]
  · simp [smithPrefixValue, conclusion_smith_local_residue_classification_blindness_spectrum111]

end Omega.Conclusion
