import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete endpoint semigroup package for Koenigs-depth rigidity. -/
structure dephys_endpoint_koenigs_rigidity_data where
  dephys_endpoint_koenigs_rigidity_State : Type u
  dephys_endpoint_koenigs_rigidity_endpoint : dephys_endpoint_koenigs_rigidity_State
  dephys_endpoint_koenigs_rigidity_mobius :
    Nat -> dephys_endpoint_koenigs_rigidity_State ->
      dephys_endpoint_koenigs_rigidity_State
  dephys_endpoint_koenigs_rigidity_halfPlane :
    dephys_endpoint_koenigs_rigidity_State -> Real
  dephys_endpoint_koenigs_rigidity_koenigs :
    dephys_endpoint_koenigs_rigidity_State -> Real
  dephys_endpoint_koenigs_rigidity_candidate :
    dephys_endpoint_koenigs_rigidity_State -> Real
  dephys_endpoint_koenigs_rigidity_depth :
    dephys_endpoint_koenigs_rigidity_State -> Real
  dephys_endpoint_koenigs_rigidity_multiplier : Nat -> Real
  dephys_endpoint_koenigs_rigidity_endpointMultiplier : Real
  dephys_endpoint_koenigs_rigidity_contractionIndex : Nat
  dephys_endpoint_koenigs_rigidity_semigroup_law :
    forall m n x,
      dephys_endpoint_koenigs_rigidity_mobius (m + n) x =
        dephys_endpoint_koenigs_rigidity_mobius m
          (dephys_endpoint_koenigs_rigidity_mobius n x)
  dephys_endpoint_koenigs_rigidity_endpoint_fixed :
    forall n,
      dephys_endpoint_koenigs_rigidity_mobius n
          dephys_endpoint_koenigs_rigidity_endpoint =
        dephys_endpoint_koenigs_rigidity_endpoint
  dephys_endpoint_koenigs_rigidity_endpoint_multiplier :
    dephys_endpoint_koenigs_rigidity_multiplier
        dephys_endpoint_koenigs_rigidity_contractionIndex =
      dephys_endpoint_koenigs_rigidity_endpointMultiplier
  dephys_endpoint_koenigs_rigidity_multiplier_law :
    forall m n,
      dephys_endpoint_koenigs_rigidity_multiplier (m + n) =
        dephys_endpoint_koenigs_rigidity_multiplier m *
          dephys_endpoint_koenigs_rigidity_multiplier n
  dephys_endpoint_koenigs_rigidity_halfPlane_law :
    forall n x,
      dephys_endpoint_koenigs_rigidity_halfPlane
          (dephys_endpoint_koenigs_rigidity_mobius n x) =
        dephys_endpoint_koenigs_rigidity_multiplier n *
          dephys_endpoint_koenigs_rigidity_halfPlane x
  dephys_endpoint_koenigs_rigidity_koenigs_law :
    forall n x,
      dephys_endpoint_koenigs_rigidity_koenigs
          (dephys_endpoint_koenigs_rigidity_mobius n x) =
        dephys_endpoint_koenigs_rigidity_multiplier n *
          dephys_endpoint_koenigs_rigidity_koenigs x
  dephys_endpoint_koenigs_rigidity_candidate_law :
    forall n x,
      dephys_endpoint_koenigs_rigidity_candidate
          (dephys_endpoint_koenigs_rigidity_mobius n x) =
        dephys_endpoint_koenigs_rigidity_multiplier n *
          dephys_endpoint_koenigs_rigidity_candidate x
  dephys_endpoint_koenigs_rigidity_depth_law :
    forall n x,
      dephys_endpoint_koenigs_rigidity_depth
          (dephys_endpoint_koenigs_rigidity_mobius n x) =
        dephys_endpoint_koenigs_rigidity_depth x + n

/-- Paper-facing endpoint-rigidity statement extracted from the concrete package. -/
def dephys_endpoint_koenigs_rigidity_statement
    (D : dephys_endpoint_koenigs_rigidity_data) : Prop :=
  D.dephys_endpoint_koenigs_rigidity_multiplier
      D.dephys_endpoint_koenigs_rigidity_contractionIndex =
    D.dephys_endpoint_koenigs_rigidity_endpointMultiplier
    ∧
  (forall n x,
    D.dephys_endpoint_koenigs_rigidity_halfPlane
        (D.dephys_endpoint_koenigs_rigidity_mobius n x) =
      D.dephys_endpoint_koenigs_rigidity_multiplier n *
        D.dephys_endpoint_koenigs_rigidity_halfPlane x)
    ∧
  (forall n x,
    D.dephys_endpoint_koenigs_rigidity_depth
        (D.dephys_endpoint_koenigs_rigidity_mobius n x) =
      D.dephys_endpoint_koenigs_rigidity_depth x + n)
    ∧
  (forall n x,
    D.dephys_endpoint_koenigs_rigidity_candidate
        (D.dephys_endpoint_koenigs_rigidity_mobius n x) *
        D.dephys_endpoint_koenigs_rigidity_koenigs x =
      D.dephys_endpoint_koenigs_rigidity_candidate x *
        D.dephys_endpoint_koenigs_rigidity_koenigs
          (D.dephys_endpoint_koenigs_rigidity_mobius n x))

/-- Paper label: `thm:dephys-endpoint-koenigs-rigidity`. -/
theorem paper_dephys_endpoint_koenigs_rigidity
    (D : dephys_endpoint_koenigs_rigidity_data) :
    dephys_endpoint_koenigs_rigidity_statement D := by
  refine ⟨D.dephys_endpoint_koenigs_rigidity_endpoint_multiplier, ?_, ?_, ?_⟩
  · exact D.dephys_endpoint_koenigs_rigidity_halfPlane_law
  · exact D.dephys_endpoint_koenigs_rigidity_depth_law
  · intro n x
    calc
      D.dephys_endpoint_koenigs_rigidity_candidate
          (D.dephys_endpoint_koenigs_rigidity_mobius n x) *
          D.dephys_endpoint_koenigs_rigidity_koenigs x =
          (D.dephys_endpoint_koenigs_rigidity_multiplier n *
            D.dephys_endpoint_koenigs_rigidity_candidate x) *
            D.dephys_endpoint_koenigs_rigidity_koenigs x := by
            rw [D.dephys_endpoint_koenigs_rigidity_candidate_law n x]
      _ = D.dephys_endpoint_koenigs_rigidity_candidate x *
          (D.dephys_endpoint_koenigs_rigidity_multiplier n *
            D.dephys_endpoint_koenigs_rigidity_koenigs x) := by
            ring
      _ = D.dephys_endpoint_koenigs_rigidity_candidate x *
          D.dephys_endpoint_koenigs_rigidity_koenigs
            (D.dephys_endpoint_koenigs_rigidity_mobius n x) := by
            rw [D.dephys_endpoint_koenigs_rigidity_koenigs_law n x]

end Omega.Zeta
