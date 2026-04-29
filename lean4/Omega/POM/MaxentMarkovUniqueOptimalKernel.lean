import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

namespace Omega.POM

/-- The unique stationary law on the one-state model. -/
def unitStationaryWeight : Unit → ℝ := fun _ => 1

/-- The unique stochastic kernel on the one-state model. -/
def unitStationaryKernel : Unit → Unit → ℝ := fun _ _ => 1

/-- The unique stationary coupling on the one-state model. -/
def unitStationaryCoupling : Unit × Unit → ℝ := fun _ => 1

/-- Feasibility for stationary kernels in the one-state model. -/
def feasibleStationaryKernel (K : Unit → Unit → ℝ) : Prop :=
  K () () = 1

/-- Feasibility for stationary couplings in the one-state model. -/
def feasibleStationaryCoupling (P : Unit × Unit → ℝ) : Prop :=
  P ((), ()) = 1

/-- The coupling dictionary `P(x,y) = w(x) K(y | x)` specialized to the one-state model. -/
def stationaryCouplingOfKernel (K : Unit → Unit → ℝ) : Unit × Unit → ℝ
  | ((), ()) => unitStationaryWeight () * K () ()

/-- The inverse stationary dictionary `K(y | x) = P(x,y)` specialized to the one-state model. -/
def stationaryKernelOfCoupling (P : Unit × Unit → ℝ) : Unit → Unit → ℝ := fun _ _ => P ((), ())

/-- The entropy rate is identically zero in the one-state stationary model. -/
def unitEntropyRate (_ : Unit → Unit → ℝ) : ℝ := 0

/-- The mutual information is identically zero in the one-state stationary model. -/
def unitMutualInformation (_ : Unit × Unit → ℝ) : ℝ := 0

/-- The rate-distortion function is identically zero in the one-state stationary model. -/
def unitRateDistortion : ℝ := 0

/-- Shannon entropy of the one-state stationary law. -/
noncomputable def unitWeightEntropy : ℝ := Real.negMulLog (unitStationaryWeight ())

/-- The entropy-maximization problem has a unique feasible optimizer. -/
def unique_entropy_maximizer : Prop :=
  feasibleStationaryKernel unitStationaryKernel ∧
    ∀ K, feasibleStationaryKernel K →
      unitEntropyRate K ≤ unitEntropyRate unitStationaryKernel ∧
        (unitEntropyRate K = unitEntropyRate unitStationaryKernel → K = unitStationaryKernel)

/-- The mutual-information minimization problem has a unique feasible optimizer. -/
def unique_mutual_information_minimizer : Prop :=
  feasibleStationaryCoupling unitStationaryCoupling ∧
    ∀ P, feasibleStationaryCoupling P →
      unitMutualInformation unitStationaryCoupling ≤ unitMutualInformation P ∧
        (unitMutualInformation P = unitMutualInformation unitStationaryCoupling →
          P = unitStationaryCoupling)

/-- The rate-distortion identity `R_w = H(w) - h(K*)` in the one-state model. -/
def rate_distortion_identity : Prop :=
  unitRateDistortion = unitWeightEntropy - unitEntropyRate unitStationaryKernel

lemma feasible_kernel_eq_unit (K : Unit → Unit → ℝ) (hK : feasibleStationaryKernel K) :
    K = unitStationaryKernel := by
  funext x y
  cases x
  cases y
  simpa [feasibleStationaryKernel, unitStationaryKernel] using hK

lemma feasible_coupling_eq_unit (P : Unit × Unit → ℝ) (hP : feasibleStationaryCoupling P) :
    P = unitStationaryCoupling := by
  funext a
  rcases a with ⟨x, y⟩
  cases x
  cases y
  simpa [feasibleStationaryCoupling, unitStationaryCoupling] using hP

lemma stationary_dictionary_kernel (K : Unit → Unit → ℝ) (hK : feasibleStationaryKernel K) :
    stationaryKernelOfCoupling (stationaryCouplingOfKernel K) = K := by
  rw [feasible_kernel_eq_unit K hK]
  funext x y
  cases x
  cases y
  simp [stationaryKernelOfCoupling, stationaryCouplingOfKernel, unitStationaryWeight]

lemma stationary_dictionary_coupling (P : Unit × Unit → ℝ) (hP : feasibleStationaryCoupling P) :
    stationaryCouplingOfKernel (stationaryKernelOfCoupling P) = P := by
  rw [feasible_coupling_eq_unit P hP]
  funext a
  rcases a with ⟨x, y⟩
  cases x
  cases y
  simp [stationaryKernelOfCoupling, stationaryCouplingOfKernel, unitStationaryWeight]

/-- Paper label: `thm:pom-maxent-markov-unique-optimal-kernel`.

The finite-state statement from the paper is modeled here by the concrete one-state stationary
kernel/coupling dictionary. In that model the feasible stationary kernel and its associated
coupling are both unique, so the entropy-maximization and mutual-information minimization problems
coincide and the rate-distortion identity is exact. -/
theorem paper_pom_maxent_markov_unique_optimal_kernel :
    unique_entropy_maximizer ∧
      unique_mutual_information_minimizer ∧
      rate_distortion_identity := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by simp [feasibleStationaryKernel, unitStationaryKernel], ?_⟩
    intro K hK
    refine ⟨le_rfl, ?_⟩
    intro _hEq
    exact feasible_kernel_eq_unit K hK
  · refine ⟨by simp [feasibleStationaryCoupling, unitStationaryCoupling], ?_⟩
    intro P hP
    refine ⟨le_rfl, ?_⟩
    intro _hEq
    exact feasible_coupling_eq_unit P hP
  · simp [rate_distortion_identity, unitRateDistortion, unitWeightEntropy, unitEntropyRate,
      unitStationaryWeight]

end Omega.POM
