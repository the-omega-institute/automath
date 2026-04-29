import Omega.CircleDimension.HilbertQuantumMainClosure

namespace Omega.CircleDimension

/-- Paper label: `conj:cdim-quadratic-readout-consistency`. -/
theorem paper_cdim_quadratic_readout_consistency (D : HilbertQuantumMainClosureData) :
    HilbertQuantumMainClosureData.discreteHilbertLayer D ∧
      HilbertQuantumMainClosureData.continuousSchrodingerLayer D := by
  exact paper_cdim_hilbert_quantum_main_closure D

end Omega.CircleDimension
