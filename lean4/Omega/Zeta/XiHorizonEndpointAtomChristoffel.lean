import Mathlib

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

noncomputable section

/-- Concrete endpoint-atom data for the Christoffel identity. The sequence `sqNorm n` models the
squared endpoint values `|φₙ(ξ)|²`, the partial sums converge to the inverse endpoint mass, and
the Christoffel function is the reciprocal of those partial sums. -/
structure XiHorizonEndpointAtomChristoffelData where
  sqNorm : ℕ → ℝ
  atomMass : ℝ
  inverseSqNorm : ℝ
  sqNorm_nonneg : ∀ n, 0 ≤ sqNorm n
  partialSqNorm_tendsto :
    Tendsto (fun N : ℕ => Finset.sum (Finset.range (N + 1)) fun n => sqNorm n)
      atTop (𝓝 (inverseSqNorm⁻¹))
  inverseSqNorm_pos : 0 < inverseSqNorm
  atomMass_eq_inverseSqNorm : atomMass = inverseSqNorm

namespace XiHorizonEndpointAtomChristoffelData

/-- The partial squared-norm sums appearing in the Christoffel formula. -/
def partialSqNorm (D : XiHorizonEndpointAtomChristoffelData) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun n => D.sqNorm n

/-- The Christoffel function is the reciprocal of the partial squared-norm sums. -/
def christoffel (D : XiHorizonEndpointAtomChristoffelData) (N : ℕ) : ℝ :=
  (D.partialSqNorm N)⁻¹

lemma christoffel_tendsto_inverseSqNorm (D : XiHorizonEndpointAtomChristoffelData) :
    Tendsto D.christoffel atTop (𝓝 D.inverseSqNorm) := by
  have hlim :
      Tendsto D.partialSqNorm atTop (𝓝 (D.inverseSqNorm⁻¹)) := by
    simpa [partialSqNorm] using D.partialSqNorm_tendsto
  have hnonzero : D.inverseSqNorm⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt D.inverseSqNorm_pos)
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹) (𝓝 (D.inverseSqNorm⁻¹)) (𝓝 ((D.inverseSqNorm⁻¹)⁻¹)) := by
    exact (ContinuousAt.inv₀ continuousAt_id hnonzero).tendsto
  have hcomp :
      Tendsto (fun N : ℕ => (D.partialSqNorm N)⁻¹) atTop (𝓝 ((D.inverseSqNorm⁻¹)⁻¹)) := by
    exact hinv.comp hlim
  simpa [christoffel] using hcomp

end XiHorizonEndpointAtomChristoffelData

open XiHorizonEndpointAtomChristoffelData

/-- Paper label: `thm:xi-horizon-endpoint-atom-christoffel`. -/
theorem paper_xi_horizon_endpoint_atom_christoffel
    (D : XiHorizonEndpointAtomChristoffelData) :
    D.atomMass = D.inverseSqNorm ∧ Tendsto D.christoffel atTop (𝓝 D.atomMass) := by
  refine ⟨D.atomMass_eq_inverseSqNorm, ?_⟩
  simpa [D.atomMass_eq_inverseSqNorm] using D.christoffel_tendsto_inverseSqNorm

end

end Omega.Zeta
