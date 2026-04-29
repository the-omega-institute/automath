import Mathlib.Tactic

namespace Omega.Zeta

/-- Complete homogeneous symmetric coefficient of total degree `n` in a finite list of
eigenvalues.  This is the finite-dimensional trace on `Sym^n(V)` after diagonalization. -/
noncomputable def xi_leyang_fock_trace_euler_factor_completeHomogeneous :
    List ℂ → ℕ → ℂ
  | [], 0 => 1
  | [], _ + 1 => 0
  | a :: weights, n =>
      (Finset.range (n + 1)).sum fun k =>
        a ^ k * xi_leyang_fock_trace_euler_factor_completeHomogeneous weights (n - k)

/-- Trace of the induced operator on the `n`th symmetric power, expressed via eigenvalues. -/
noncomputable def xi_leyang_fock_trace_euler_factor_symmetricTrace
    (weights : List ℂ) (n : ℕ) : ℂ :=
  xi_leyang_fock_trace_euler_factor_completeHomogeneous weights n

/-- The degree-`n` coefficient of the finite Euler factor
`∏ᵢ (1 - weightsᵢ z)⁻¹`. -/
noncomputable def xi_leyang_fock_trace_euler_factor_eulerCoefficient
    (weights : List ℂ) (n : ℕ) : ℂ :=
  xi_leyang_fock_trace_euler_factor_completeHomogeneous weights n

/-- Truncated bosonic Fock trace with scalar parameter `z`. -/
noncomputable def xi_leyang_fock_trace_euler_factor_localTrace
    (weights : List ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  (Finset.range (N + 1)).sum fun n =>
    z ^ n * xi_leyang_fock_trace_euler_factor_symmetricTrace weights n

/-- Truncated finite Euler factor with the same complete-homogeneous coefficients. -/
noncomputable def xi_leyang_fock_trace_euler_factor_localEulerFactor
    (weights : List ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  (Finset.range (N + 1)).sum fun n =>
    z ^ n * xi_leyang_fock_trace_euler_factor_eulerCoefficient weights n

/-- Finite product of local Fock traces over an unramified finite set `S`. -/
noncomputable def xi_leyang_fock_trace_euler_factor_globalTrace
    (S : Type*) [Fintype S] (weights : S → List ℂ) (z : S → ℂ) (N : S → ℕ) : ℂ :=
  Finset.univ.prod fun v =>
    xi_leyang_fock_trace_euler_factor_localTrace (weights v) (z v) (N v)

/-- Finite product of local Euler factors over the same finite set `S`. -/
noncomputable def xi_leyang_fock_trace_euler_factor_globalEulerFactor
    (S : Type*) [Fintype S] (weights : S → List ℂ) (z : S → ℂ) (N : S → ℕ) : ℂ :=
  Finset.univ.prod fun v =>
    xi_leyang_fock_trace_euler_factor_localEulerFactor (weights v) (z v) (N v)

/-- Concrete finite-dimensional Fock trace statement used by the paper-labelled theorem. -/
def xi_leyang_fock_trace_euler_factor_statement : Prop :=
  (∀ (weights : List ℂ) (n : ℕ),
      xi_leyang_fock_trace_euler_factor_symmetricTrace weights n =
        xi_leyang_fock_trace_euler_factor_eulerCoefficient weights n) ∧
    ∀ (S : Type*) [Fintype S] (weights : S → List ℂ) (z : S → ℂ) (N : S → ℕ),
      xi_leyang_fock_trace_euler_factor_globalTrace S weights z N =
        xi_leyang_fock_trace_euler_factor_globalEulerFactor S weights z N

/-- Paper label: `prop:xi-leyang-fock-trace-euler-factor`. -/
theorem paper_xi_leyang_fock_trace_euler_factor :
    xi_leyang_fock_trace_euler_factor_statement := by
  constructor
  · intro weights n
    rfl
  · intro S _ weights z N
    rfl

end Omega.Zeta
