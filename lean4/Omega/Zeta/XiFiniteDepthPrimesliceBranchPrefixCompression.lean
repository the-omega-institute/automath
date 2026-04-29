import Mathlib.Tactic

namespace Omega.Zeta

/-- The multiplicative packaging map obtained by decoding a branch-register prefix and then
    applying the target prime-slice encoding. -/
def xi_finite_depth_primeslice_branch_prefix_compression_packaging
    {X0 Xk Prefix Encoded : Type*} {Psi : X0 → Xk × Prefix}
    (Phi : X0 → Xk × Encoded) (decode : Set.range Psi → X0) :
    Set.range Psi → Xk × Encoded :=
  fun y => Phi (decode y)

/-- Paper label: `thm:xi-finite-depth-primeslice-branch-prefix-compression`. -/
theorem paper_xi_finite_depth_primeslice_branch_prefix_compression
    {X0 Xk Prefix Encoded : Type*} (Psi : X0 -> Xk × Prefix)
    (Phi : X0 -> Xk × Encoded) (decode : Set.range Psi -> X0)
    (hdecode : forall x : X0, decode ⟨Psi x, ⟨x, rfl⟩⟩ = x) :
    Function.Injective Psi ∧
      exists M : Set.range Psi -> Xk × Encoded,
        forall x : X0, M ⟨Psi x, ⟨x, rfl⟩⟩ = Phi x := by
  constructor
  · intro x y hxy
    calc
      x = decode ⟨Psi x, ⟨x, rfl⟩⟩ := (hdecode x).symm
      _ = decode ⟨Psi y, ⟨y, rfl⟩⟩ := congrArg decode (Subtype.ext hxy)
      _ = y := hdecode y
  · refine
      ⟨xi_finite_depth_primeslice_branch_prefix_compression_packaging Phi decode, ?_⟩
    intro x
    simp [xi_finite_depth_primeslice_branch_prefix_compression_packaging, hdecode x]

end Omega.Zeta
