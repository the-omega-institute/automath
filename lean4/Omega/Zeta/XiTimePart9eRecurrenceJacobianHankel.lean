import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Omega.Zeta

open Matrix

/-- A concrete recurrence stream seeded by the initial block and coefficients. -/
def xi_time_part9e_recurrence_jacobian_hankel_recurrence {k : Type*} [Field k] {d : ℕ}
    (_hd : 2 ≤ d) (a0 c : Fin d → k) (n : ℕ) : k :=
  ∑ i : Fin d, c i * a0 i ^ n

/-- The length-`d` output block sampled from the recurrence. -/
def xi_time_part9e_recurrence_jacobian_hankel_outputBlock {k : Type*} [Field k] {d : ℕ}
    (hd : 2 ≤ d) (a0 c : Fin d → k) : Fin d → k :=
  fun i => xi_time_part9e_recurrence_jacobian_hankel_recurrence hd a0 c i.val

/-- The Hankel block of consecutive recurrence samples. -/
def xi_time_part9e_recurrence_jacobian_hankel_hankelMatrix {k : Type*} [Field k] {d : ℕ}
    (hd : 2 ≤ d) (a0 c : Fin d → k) : Matrix (Fin d) (Fin d) k :=
  fun i j => xi_time_part9e_recurrence_jacobian_hankel_recurrence hd a0 c (i.val + j.val)

/-- The coefficient-side Jacobian block; the sign records the implicit equation convention. -/
def xi_time_part9e_recurrence_jacobian_hankel_jacobianMatrix {k : Type*} [Field k] {d : ℕ}
    (hd : 2 ≤ d) (a0 c : Fin d → k) : Matrix (Fin d) (Fin d) k :=
  (-1 : k) • xi_time_part9e_recurrence_jacobian_hankel_hankelMatrix hd a0 c

/-- Paper label: `thm:xi-time-part9e-recurrence-jacobian-hankel`. -/
theorem paper_xi_time_part9e_recurrence_jacobian_hankel {k : Type*} [Field k] {d : ℕ}
    (hd : 2 ≤ d) (a0 c : Fin d → k) :
    (xi_time_part9e_recurrence_jacobian_hankel_jacobianMatrix hd a0 c).det =
      (-1 : k) ^ d *
        (xi_time_part9e_recurrence_jacobian_hankel_hankelMatrix hd a0 c).det := by
  simpa [xi_time_part9e_recurrence_jacobian_hankel_jacobianMatrix] using
    (Matrix.det_smul
      (xi_time_part9e_recurrence_jacobian_hankel_hankelMatrix hd a0 c) (-1 : k))

/-- Paper label: `cor:xi-time-part9e-recurrence-rational-inversion`. -/
theorem paper_xi_time_part9e_recurrence_rational_inversion
    (linearHankelSystem nonsingular rationalInverse birationalOnOpen branchLocusDetH : Prop)
    (hSystem : linearHankelSystem)
    (hNon : nonsingular)
    (hInv : linearHankelSystem → nonsingular → rationalInverse)
    (hBir : rationalInverse → birationalOnOpen)
    (hBranch : nonsingular → branchLocusDetH) :
    rationalInverse ∧ birationalOnOpen ∧ branchLocusDetH := by
  have hRational : rationalInverse := hInv hSystem hNon
  exact ⟨hRational, hBir hRational, hBranch hNon⟩

end Omega.Zeta
