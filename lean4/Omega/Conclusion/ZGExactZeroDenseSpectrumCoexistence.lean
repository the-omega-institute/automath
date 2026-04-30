import Omega.Conclusion.ZGPushforwardExactDimensionZero
import Omega.Conclusion.ConclusionZGZeroInfiniteLocalDimensionTopologicalCoexistence

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zg-exact-zero-dense-spectrum-coexistence`. -/
theorem paper_conclusion_zg_exact_zero_dense_spectrum_coexistence
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data)
    (aeLocalDimensionZero exactDimensionalZero : Prop) (hAe : aeLocalDimensionZero)
    (hExact : aeLocalDimensionZero → exactDimensionalZero) :
    exactDimensionalZero ∧ D.zeroLayerDense ∧ D.infiniteLayerDenseGdelta := by
  have hExactDimensionalZero : exactDimensionalZero :=
    paper_conclusion_zg_pushforward_exact_dimension_zero
      aeLocalDimensionZero exactDimensionalZero hExact hAe
  have hCoexistence :=
    paper_conclusion_zg_zero_infinite_local_dimension_topological_coexistence D
  exact ⟨hExactDimensionalZero, hCoexistence.1, hCoexistence.2⟩

end Omega.Conclusion
