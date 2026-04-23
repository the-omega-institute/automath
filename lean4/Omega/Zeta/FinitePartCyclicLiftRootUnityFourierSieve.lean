import Omega.Zeta.FinitePartCyclicLiftTraceSieve

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cyclic-lift root-of-unity Fourier sieve in the ETDS
finite-part section: the trace-normalized multiple-sum expansion is first obtained from the
existing trace-sieve package, then root-of-unity orthogonality isolates the residue-class
components of the non-Perron spectral sums.
    prop:finite-part-cyclic-lift-root-unity-fourier-sieve -/
theorem paper_etds_finite_part_cyclic_lift_root_unity_fourier_sieve
    (traceNormalization dirichletMultipleSum rootUnityOrthogonality congruenceClassIsolation
      nonPerronSpectralSums : Prop)
    (hTrace : traceNormalization)
    (hDirichlet : traceNormalization → dirichletMultipleSum)
    (hOrthogonality : dirichletMultipleSum → rootUnityOrthogonality)
    (hCongruence : rootUnityOrthogonality → congruenceClassIsolation)
    (hSpectral : congruenceClassIsolation → nonPerronSpectralSums) :
    dirichletMultipleSum ∧ rootUnityOrthogonality ∧ congruenceClassIsolation ∧
      nonPerronSpectralSums := by
  have hTraceSieve :=
    paper_etds_finite_part_cyclic_lift_trace_sieve
      traceNormalization dirichletMultipleSum rootUnityOrthogonality
      hTrace hDirichlet hOrthogonality
  have hClass : congruenceClassIsolation := hCongruence hTraceSieve.2
  exact ⟨hTraceSieve.1, hTraceSieve.2, hClass, hSpectral hClass⟩

/-- Paper label: `prop:finite-part-cyclic-lift-root-unity-fourier-sieve`. -/
theorem paper_finite_part_cyclic_lift_root_unity_fourier_sieve
    (traceNormalization dirichletMultipleSum rootUnityOrthogonality congruenceClassIsolation
      nonPerronSpectralSums : Prop)
    (hTrace : traceNormalization)
    (hDirichlet : traceNormalization → dirichletMultipleSum)
    (hOrthogonality : dirichletMultipleSum → rootUnityOrthogonality)
    (hCongruence : rootUnityOrthogonality → congruenceClassIsolation)
    (hSpectral : congruenceClassIsolation → nonPerronSpectralSums) :
    dirichletMultipleSum ∧ rootUnityOrthogonality ∧ congruenceClassIsolation ∧
      nonPerronSpectralSums := by
  exact
    paper_etds_finite_part_cyclic_lift_root_unity_fourier_sieve
      traceNormalization dirichletMultipleSum rootUnityOrthogonality congruenceClassIsolation
      nonPerronSpectralSums hTrace hDirichlet hOrthogonality hCongruence hSpectral

end Omega.Zeta
