import Mathlib.Tactic
import Omega.Conclusion.SmithLocalZetaPoleResidueHeadTriple

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-smith-unimodular-residue-rigidity`. -/
theorem paper_conclusion_smith_unimodular_residue_rigidity {m : ℕ} (e : Fin m → ℕ) :
    ((∀ i, e i = 0) ↔ ∑ i, e i = 0) ∧
      ((∑ i, e i = 0) ↔
        ∀ p : ℕ, conclusion_smith_local_zeta_pole_residue_head_triple_residue p e = 1) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro he
      simp [he]
    · intro hsum i
      have he : e = 0 := (Fintype.sum_eq_zero_iff_of_nonneg fun j => Nat.zero_le (e j)).mp hsum
      simpa using congrFun he i
  · constructor
    · intro hsum p
      simp [conclusion_smith_local_zeta_pole_residue_head_triple_residue, hsum]
    · intro hres
      by_contra hsum
      have hpos : 0 < ∑ i, e i := Nat.pos_of_ne_zero hsum
      have hzero : (0 : ℝ) = 1 := by
        simpa [conclusion_smith_local_zeta_pole_residue_head_triple_residue, hpos.ne'] using
          hres 0
      exact zero_ne_one hzero

end Omega.Conclusion
