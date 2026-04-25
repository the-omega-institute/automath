import Mathlib.Tactic
import Omega.Zeta.XiLocalJetDeterminesFiniteCMVAndToeplitzCertificate

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete endpoint-atom data for the logarithmic jet-depth package. The local jet determines
the Toeplitz certificate up to depth `N`; the tail estimate and the threshold inequality are
recorded as explicit scalar bounds on the jet-determined coefficient `a_N`. -/
structure xi_point_atom_endpoint_jet_depth_logarithmic_data where
  ell : ℕ → ℝ
  coeff : ℕ → ℝ
  coeff_zero : coeff 0 = -ell 1
  coeff_one : coeff 1 = -ell 2
  coeff_two : coeff 2 = ell 2 - ell 3
  coeff_zero_pos : 0 < coeff 0
  N : ℕ
  delta0 : ℝ
  hdelta0 : 0 < delta0
  atomMass : ℝ
  muK : ℝ
  qK : ℝ
  epsilon : ℝ
  tail_bound :
    xiFiniteToeplitzDetPrefix ell N delta0 hdelta0 ⟨N, Nat.lt_succ_self N⟩ - atomMass ≤
      muK * qK ^ (2 * N)
  threshold_bound : muK * qK ^ (2 * N) ≤ epsilon

/-- The finite Toeplitz determinant package read off from the endpoint jet. -/
def xi_point_atom_endpoint_jet_depth_logarithmic_toeplitzData
    (D : xi_point_atom_endpoint_jet_depth_logarithmic_data) : XiToeplitzDetVerblunskyData :=
  xiToeplitzDetDataFromJet D.ell D.N D.delta0 D.hdelta0

/-- The jet-determined coefficient `a_N`. -/
def xi_point_atom_endpoint_jet_depth_logarithmic_aN
    (D : xi_point_atom_endpoint_jet_depth_logarithmic_data) : ℝ :=
  xiFiniteToeplitzDetPrefix D.ell D.N D.delta0 D.hdelta0 ⟨D.N, Nat.lt_succ_self D.N⟩

/-- Paper-facing statement for the endpoint-atom logarithmic depth estimate. -/
def xi_point_atom_endpoint_jet_depth_logarithmic_statement
    (D : xi_point_atom_endpoint_jet_depth_logarithmic_data) : Prop :=
  let T := xi_point_atom_endpoint_jet_depth_logarithmic_toeplitzData D
  let mN : Fin (D.N + 1) := ⟨D.N, Nat.lt_succ_self D.N⟩
  xi_point_atom_endpoint_jet_depth_logarithmic_aN D =
      D.delta0 * Finset.prod (Finset.range mN) T.stepFactor ∧
    xi_point_atom_endpoint_jet_depth_logarithmic_aN D - D.atomMass ≤
      D.muK * D.qK ^ (2 * D.N) ∧
    xi_point_atom_endpoint_jet_depth_logarithmic_aN D ≤ D.atomMass + D.epsilon

/-- Paper label: `thm:xi-point-atom-endpoint-jet-depth-logarithmic`. The endpoint jet determines
the Toeplitz coefficient `a_N` via the finite CMV/Toeplitz certificate, and the explicit tail and
threshold bounds combine to give the advertised depth estimate. -/
theorem paper_xi_point_atom_endpoint_jet_depth_logarithmic
    (D : xi_point_atom_endpoint_jet_depth_logarithmic_data) :
    xi_point_atom_endpoint_jet_depth_logarithmic_statement D := by
  let T := xi_point_atom_endpoint_jet_depth_logarithmic_toeplitzData D
  let mN : Fin (D.N + 1) := ⟨D.N, Nat.lt_succ_self D.N⟩
  have hLocal :=
    paper_xi_local_jet_determines_finite_cmv_and_toeplitz_certificate
      D.ell D.coeff D.coeff_zero D.coeff_one D.coeff_two D.coeff_zero_pos D.N D.delta0 D.hdelta0
  rcases hLocal with ⟨_, _, _, hToeplitz, _, _, _⟩
  have hFormula :
      xi_point_atom_endpoint_jet_depth_logarithmic_aN D =
        D.delta0 * Finset.prod (Finset.range mN) T.stepFactor := by
    simpa [xi_point_atom_endpoint_jet_depth_logarithmic_aN,
      xi_point_atom_endpoint_jet_depth_logarithmic_toeplitzData, T, mN] using hToeplitz mN
  have hTailToEpsilon :
      xi_point_atom_endpoint_jet_depth_logarithmic_aN D - D.atomMass ≤ D.epsilon :=
    le_trans D.tail_bound D.threshold_bound
  refine ⟨hFormula, D.tail_bound, ?_⟩
  linarith

end

end Omega.Zeta
