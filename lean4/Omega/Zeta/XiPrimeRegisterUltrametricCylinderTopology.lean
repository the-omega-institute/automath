import Omega.SPG.PrefixMetric

namespace Omega.Zeta

open Omega.SPG

noncomputable section

/-- The prime-register stream model is represented by the existing binary prefix space. -/
abbrev xi_prime_register_ultrametric_cylinder_topology_stream :=
  OmegaInfinity

/-- Prime-register distance: first differing register coordinate gives the prefix ultrametric. -/
noncomputable def xi_prime_register_ultrametric_cylinder_topology_dist
    (x y : xi_prime_register_ultrametric_cylinder_topology_stream) : ℝ :=
  prefixDist x y

/-- Finite-prefix cylinder centered at a prime-register stream. -/
def xi_prime_register_ultrametric_cylinder_topology_cylinder
    (x : xi_prime_register_ultrametric_cylinder_topology_stream) (m : ℕ) :
    Set xi_prime_register_ultrametric_cylinder_topology_stream :=
  prefixBall x m

/-- Decoded prime-register streams whose finite prefixes are stable. In this concrete prefix model
the decoded image is the full stream space. -/
def xi_prime_register_ultrametric_cylinder_topology_decodedImage :
    Set xi_prime_register_ultrametric_cylinder_topology_stream :=
  Set.univ

/-- The completion target is the product-topology closure of the prefix-stable decoded image. -/
def xi_prime_register_ultrametric_cylinder_topology_completionTarget :
    Set xi_prime_register_ultrametric_cylinder_topology_stream :=
  closure xi_prime_register_ultrametric_cylinder_topology_decodedImage

/-- Concrete statement for the prime-register ultrametric/cylinder topology package. -/
def xi_prime_register_ultrametric_cylinder_topology_statement : Prop :=
  (∀ x y z : xi_prime_register_ultrametric_cylinder_topology_stream,
      xi_prime_register_ultrametric_cylinder_topology_dist x z ≤
        max (xi_prime_register_ultrametric_cylinder_topology_dist x y)
          (xi_prime_register_ultrametric_cylinder_topology_dist y z)) ∧
    (∀ x y : xi_prime_register_ultrametric_cylinder_topology_stream,
      xi_prime_register_ultrametric_cylinder_topology_dist x y = 0 ↔ x = y) ∧
    (∀ (x : xi_prime_register_ultrametric_cylinder_topology_stream) (m : ℕ),
      xi_prime_register_ultrametric_cylinder_topology_cylinder x m =
        {y | xi_prime_register_ultrametric_cylinder_topology_dist y x ≤ (1 / 2 : ℝ) ^ m}) ∧
    xi_prime_register_ultrametric_cylinder_topology_completionTarget = Set.univ

/-- Paper label: `thm:xi-prime-register-ultrametric-cylinder-topology`. -/
theorem paper_xi_prime_register_ultrametric_cylinder_topology :
    xi_prime_register_ultrametric_cylinder_topology_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    exact prefixDist_ultrametric x y z
  · intro x y
    exact prefixDist_eq_zero_iff x y
  · intro x m
    exact prefixBall_eq_closedBall x m
  · simp [xi_prime_register_ultrametric_cylinder_topology_completionTarget,
      xi_prime_register_ultrametric_cylinder_topology_decodedImage]

end

end Omega.Zeta
