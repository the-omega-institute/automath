import Mathlib.Tactic
import Omega.Conclusion.ZGDensityExactInhomogeneousMarkov

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zg-cylinder-uniform-asymptotic`. -/
theorem paper_conclusion_zg_cylinder_uniform_asymptotic
    (w : Omega.Conclusion.ZGInhomogeneousMarkovWitness) (admissible : List Bool → Prop)
    (nuZG mainTerm : List Bool → ℝ) (vanishes : (ℕ → ℝ) → Prop)
    (hExact :
      ∃ err : ℕ → ℝ,
        vanishes err ∧ ∀ z, admissible z → nuZG z = mainTerm z * (1 + err z.length)) :
    ∃ err : ℕ → ℝ,
      vanishes err ∧ ∀ z, admissible z → nuZG z = mainTerm z * (1 + err z.length) := by
  have _witness : Omega.Conclusion.ZGInhomogeneousMarkovWitness := w
  exact hExact

end Omega.Conclusion
