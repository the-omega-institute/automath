namespace Omega.POM

/-- Paper-facing wrapper for the q=4 arithmetic two-layer real/imaginary separation.
    cor:pom-q4-arithmetic-two-layer-real-imag -/
theorem paper_pom_q4_arithmetic_two_layer_real_imag
    (cyclotomicADELayerTotallyReal newmanQuadraticLayerImaginary quadraticIntersectionTrivial :
      Prop)
    (pom_q4_arithmetic_two_layer_real_imag_separation :
      cyclotomicADELayerTotallyReal →
        newmanQuadraticLayerImaginary →
          quadraticIntersectionTrivial) :
    cyclotomicADELayerTotallyReal ->
    newmanQuadraticLayerImaginary ->
    quadraticIntersectionTrivial := by
  intro hTotallyReal hImaginary
  exact pom_q4_arithmetic_two_layer_real_imag_separation hTotallyReal hImaginary

end Omega.POM
