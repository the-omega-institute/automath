import Mathlib.Tactic
import Omega.Conclusion.JGGodelLoglatticeApproximation
import Omega.Conclusion.JgSlitUniformizationOrthogonalCoordinates
import Omega.Conclusion.TwoPrimeDenseOrbitHyperbolaLeaf

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-jg-godel-dense-orbits-on-hyperbola-leaf`.
The already verified two-prime dense-orbit package gives the hyperbola-leaf density statement,
while the orthogonal Joukowsky chart supplies the explicit parametrization of the leaf; together
they provide the paper-facing dense-orbit theorem. -/
theorem paper_conclusion_jg_godel_dense_orbits_on_hyperbola_leaf :
    (∀ w : conclusion_jg_godel_loglattice_approximation_witness,
      conclusion_jg_godel_loglattice_approximation_statement w) ∧
      conclusion_two_prime_dense_orbit_hyperbola_leaf_statement ∧
      ∀ u θ : ℝ,
        0 < u →
          Real.sin θ ≠ 0 →
            Real.cos θ ≠ 0 →
              conclusion_jg_slit_uniformization_orthogonal_coordinates_w u θ =
                Complex.mk (2 * Real.cosh u * Real.cos θ) (2 * Real.sinh u * Real.sin θ) := by
  refine ⟨?_, paper_conclusion_two_prime_dense_orbit_hyperbola_leaf, ?_⟩
  · intro w
    exact paper_conclusion_jg_godel_loglattice_approximation w
  · intro u θ hu hsin hcos
    exact (paper_conclusion_jg_slit_uniformization_orthogonal_coordinates u θ hu hsin hcos).1

end Omega.Conclusion
