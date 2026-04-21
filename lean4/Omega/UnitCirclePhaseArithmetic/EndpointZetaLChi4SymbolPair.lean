import Omega.UnitCirclePhaseArithmetic.EndpointDirichletSymbolWeights

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete endpoint `L(1 + σ, χ₄)` symbol used by the odd endpoint package. -/
def endpointLChi4Symbol (σ : ℝ) : ℝ :=
  endpointOddClassSum σ

/-- The endpoint even observable splits through the three residue-class channels. -/
def endpointEvenSymbolDecomposition (σ : ℝ) (g : Int → ℝ) : Prop :=
  endpointRegularizedChannelOperator σ g =
    endpointOddClassSum σ * g 0 +
      endpointZeroModFourClassSum σ * g 2 +
      endpointTwoModFourClassSum σ * g (-2)

/-- The mod-`4` character on endpoint channels. -/
def endpointChi4Sign (m : ℕ) : ℤ :=
  if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0

/-- On odd indices, the endpoint odd functional is an eigenvector for the `χ₄`-twist, with the
explicit endpoint symbol as eigenvalue. -/
def endpointOddChi4WeightedSign (σ : ℝ) (m : ℕ) : ℝ :=
  endpointLChi4Symbol σ * endpointChi4Sign m

/-- The odd endpoint channel is the one-dimensional `χ₄` eigenspace: residue classes `1 mod 4` and
`3 mod 4` carry the two signs, while even channels vanish. -/
def endpointOddChi4Eigen (σ : ℝ) : Prop :=
  (∀ k, endpointOddChi4WeightedSign σ (4 * k + 1) = endpointLChi4Symbol σ) ∧
    (∀ k, endpointOddChi4WeightedSign σ (4 * k + 3) = -endpointLChi4Symbol σ) ∧
    (∀ k, endpointOddChi4WeightedSign σ (2 * k) = 0)

/-- The endpoint package splits into the explicit even `ζ`-symbol decomposition together with the
odd `χ₄` eigen-relation.  The first component reuses the three-channel endpoint split, while the
second component packages the odd Chebyshev endpoint identity as a one-dimensional eigenvector.
    thm:endpoint-zeta-Lchi4-symbol-pair -/
theorem paper_endpoint_zeta_lchi4_symbol_pair (σ : ℝ) (g : Int → ℝ) :
    endpointEvenSymbolDecomposition σ g ∧ endpointOddChi4Eigen σ := by
  refine ⟨?_, ?_⟩
  · exact (paper_endpoint_dirichlet_symbol_weights σ g).1
  · refine ⟨?_, ?_, ?_⟩
    · intro k
      have h1 : (4 * k + 1) % 4 = 1 := by omega
      simp [endpointOddChi4WeightedSign, endpointChi4Sign, h1]
    · intro k
      have h3 : (4 * k + 3) % 4 = 3 := by omega
      simp [endpointOddChi4WeightedSign, endpointChi4Sign, h3]
    · intro k
      have hneq1 : (2 * k) % 4 ≠ 1 := by omega
      have hneq3 : (2 * k) % 4 ≠ 3 := by omega
      simp [endpointOddChi4WeightedSign, endpointChi4Sign, hneq1, hneq3]

end

end Omega.UnitCirclePhaseArithmetic
