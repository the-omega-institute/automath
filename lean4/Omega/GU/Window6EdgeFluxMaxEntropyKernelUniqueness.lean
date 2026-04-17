import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

/-- The audited four-state quotient used for the window-`6` edge-flux kernel audit. -/
abbrev Window6EdgeFluxState := Fin 4

/-- Audited reversible kernel on the four-state edge-flux quotient. -/
def window6EdgeFluxAuditKernel :
    Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1 / 2
    | 0, 1 => 1 / 4
    | 0, 3 => 1 / 4
    | 1, 0 => 1 / 4
    | 1, 1 => 1 / 2
    | 1, 2 => 1 / 4
    | 2, 1 => 1 / 4
    | 2, 2 => 1 / 2
    | 2, 3 => 1 / 4
    | 3, 0 => 1 / 4
    | 3, 2 => 1 / 4
    | 3, 3 => 1 / 2
    | _, _ => 0

/-- The audited stationary law is uniform on the four visible edge states. -/
def window6EdgeFluxAuditStationary (_ : Window6EdgeFluxState) : ℚ :=
  1 / 4

/-- Audited off-diagonal edge fluxes. -/
def window6EdgeFluxAuditFlux (i j : Window6EdgeFluxState) : ℚ :=
  window6EdgeFluxAuditStationary i * window6EdgeFluxAuditKernel i j

/-- Row-stochasticity for a finite-state kernel. -/
def Window6EdgeFluxRowStochastic
    (K : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ) : Prop :=
  ∀ i, ∑ j, K i j = 1

/-- Off-diagonal edge-flux constraints for the audited window-`6` package. -/
def Window6EdgeFluxOffDiagonalFlows
    (K : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ) : Prop :=
  ∀ i j, i ≠ j →
    window6EdgeFluxAuditStationary i * K i j = window6EdgeFluxAuditFlux i j

/-- Feasibility means matching the audited off-diagonal fluxes and having unit row sums. -/
def Window6EdgeFluxFeasibleKernel
    (K : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ) : Prop :=
  Window6EdgeFluxRowStochastic K ∧ Window6EdgeFluxOffDiagonalFlows K

/-- Concrete data for the audited entropy-maximizing edge-flux kernel. -/
structure Window6EdgeFluxMaxEntropyKernelData where
  kernel : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ
  audited_kernel : kernel = window6EdgeFluxAuditKernel

/-- The paper kernel matches the audited four-state solution. -/
def Window6EdgeFluxMaxEntropyKernelData.kernelMatchesAudit
    (D : Window6EdgeFluxMaxEntropyKernelData) : Prop :=
  D.kernel = window6EdgeFluxAuditKernel

/-- Detailed balance for the audited stationary law. -/
def Window6EdgeFluxMaxEntropyKernelData.detailedBalance
    (D : Window6EdgeFluxMaxEntropyKernelData) : Prop :=
  ∀ i j,
    window6EdgeFluxAuditStationary i * D.kernel i j =
      window6EdgeFluxAuditStationary j * D.kernel j i

/-- Uniqueness of the feasible kernel implies uniqueness of the entropy maximizer. -/
def Window6EdgeFluxMaxEntropyKernelData.uniqueEntropyMaximizer
    (D : Window6EdgeFluxMaxEntropyKernelData) : Prop :=
  ∀ K, Window6EdgeFluxFeasibleKernel K → K = D.kernel

private theorem window6EdgeFluxAuditKernel_rowStochastic :
    Window6EdgeFluxRowStochastic window6EdgeFluxAuditKernel := by
  intro i
  fin_cases i <;> norm_num [window6EdgeFluxAuditKernel, Fin.sum_univ_four]

private theorem window6EdgeFluxAuditKernel_symm (i j : Window6EdgeFluxState) :
    window6EdgeFluxAuditKernel i j = window6EdgeFluxAuditKernel j i := by
  fin_cases i <;> fin_cases j <;> norm_num [window6EdgeFluxAuditKernel]

private theorem window6EdgeFlux_offDiag_eq_audit
    {K : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ}
    (hK : Window6EdgeFluxFeasibleKernel K) {i j : Window6EdgeFluxState} (hij : i ≠ j) :
    K i j = window6EdgeFluxAuditKernel i j := by
  have hflux : window6EdgeFluxAuditStationary i * K i j = window6EdgeFluxAuditFlux i j :=
    hK.2 i j hij
  have hscaled := congrArg (fun x : ℚ => (4 : ℚ) * x) hflux
  simpa [window6EdgeFluxAuditFlux, window6EdgeFluxAuditStationary, mul_assoc] using hscaled

private theorem window6EdgeFlux_diag_eq_audit
    {K : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ}
    (hK : Window6EdgeFluxFeasibleKernel K) (i : Window6EdgeFluxState) :
    K i i = window6EdgeFluxAuditKernel i i := by
  fin_cases i
  · have h01 := window6EdgeFlux_offDiag_eq_audit hK (i := 0) (j := 1) (by decide)
    have h02 := window6EdgeFlux_offDiag_eq_audit hK (i := 0) (j := 2) (by decide)
    have h03 := window6EdgeFlux_offDiag_eq_audit hK (i := 0) (j := 3) (by decide)
    norm_num [window6EdgeFluxAuditKernel] at h01 h02 h03
    have hrow : K 0 0 + K 0 1 + K 0 2 + K 0 3 = 1 := by
      simpa [Fin.sum_univ_four] using
        hK.1 (0 : Window6EdgeFluxState)
    change K 0 0 = 1 / 2
    linarith
  · have h10 := window6EdgeFlux_offDiag_eq_audit hK (i := 1) (j := 0) (by decide)
    have h12 := window6EdgeFlux_offDiag_eq_audit hK (i := 1) (j := 2) (by decide)
    have h13 := window6EdgeFlux_offDiag_eq_audit hK (i := 1) (j := 3) (by decide)
    norm_num [window6EdgeFluxAuditKernel] at h10 h12 h13
    have hrow : K 1 0 + K 1 1 + K 1 2 + K 1 3 = 1 := by
      simpa [Fin.sum_univ_four] using hK.1 (1 : Window6EdgeFluxState)
    change K 1 1 = 1 / 2
    linarith [h10, h12, h13]
  · have h20 := window6EdgeFlux_offDiag_eq_audit hK (i := 2) (j := 0) (by decide)
    have h21 := window6EdgeFlux_offDiag_eq_audit hK (i := 2) (j := 1) (by decide)
    have h23 := window6EdgeFlux_offDiag_eq_audit hK (i := 2) (j := 3) (by decide)
    norm_num [window6EdgeFluxAuditKernel] at h20 h21 h23
    have hrow : K 2 0 + K 2 1 + K 2 2 + K 2 3 = 1 := by
      simpa [Fin.sum_univ_four] using hK.1 (2 : Window6EdgeFluxState)
    change K 2 2 = 1 / 2
    linarith [h20, h21, h23]
  · have h30 := window6EdgeFlux_offDiag_eq_audit hK (i := 3) (j := 0) (by decide)
    have h31 := window6EdgeFlux_offDiag_eq_audit hK (i := 3) (j := 1) (by decide)
    have h32 := window6EdgeFlux_offDiag_eq_audit hK (i := 3) (j := 2) (by decide)
    norm_num [window6EdgeFluxAuditKernel] at h30 h31 h32
    have hrow : K 3 0 + K 3 1 + K 3 2 + K 3 3 = 1 := by
      simpa [Fin.sum_univ_four] using hK.1 (3 : Window6EdgeFluxState)
    change K 3 3 = 1 / 2
    linarith [h30, h31, h32]

private theorem window6EdgeFlux_feasible_eq_audit
    {K : Matrix Window6EdgeFluxState Window6EdgeFluxState ℚ}
    (hK : Window6EdgeFluxFeasibleKernel K) :
    K = window6EdgeFluxAuditKernel := by
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using window6EdgeFlux_diag_eq_audit hK i
  · exact window6EdgeFlux_offDiag_eq_audit hK hij

/-- Paper label: `cor:window6-edge-flux-max-entropy-kernel-uniqueness`. -/
theorem paper_window6_edge_flux_max_entropy_kernel_uniqueness
    (D : Window6EdgeFluxMaxEntropyKernelData) :
    D.kernelMatchesAudit ∧ D.detailedBalance ∧ D.uniqueEntropyMaximizer := by
  refine ⟨D.audited_kernel, ?_, ?_⟩
  · intro i j
    rw [D.audited_kernel]
    simpa [window6EdgeFluxAuditStationary, mul_assoc] using
      congrArg (fun x : ℚ => window6EdgeFluxAuditStationary i * x)
        (window6EdgeFluxAuditKernel_symm i j)
  · intro K hK
    calc
      K = window6EdgeFluxAuditKernel := window6EdgeFlux_feasible_eq_audit hK
      _ = D.kernel := D.audited_kernel.symm

end Omega.GU
