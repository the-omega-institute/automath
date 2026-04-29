import Omega.Conclusion.ScreenAuditGapSupermodularity
import Omega.SPG.ScreenKernelAuditCost
import Omega.SPG.ScreenKernelConnectedComponents


namespace Omega.Conclusion

open Finset

/-- Total connected-component count for the fixed-resolution axial screen. -/
def fixedResolutionScreenComponents (m n : ℕ) : ℕ :=
  2 ^ (m * (n - 1)) + 1

/-- Kernel corank for the fixed-resolution axial screen. -/
def fixedResolutionScreenKernelRank (m n : ℕ) : ℕ :=
  fixedResolutionScreenComponents m n - 1

/-- Relative-homology rank, using the trivial-boundary quotient from the SPG package. -/
def fixedResolutionScreenHomologyRank (m n : ℕ) : ℕ :=
  fixedResolutionScreenKernelRank m n - 0

/-- Minimal audit cost needed to reconnect the fixed-resolution screen. -/
def fixedResolutionScreenAuditCost (m n : ℕ) : ℕ :=
  fixedResolutionScreenComponents m n - 1

/-- Monotonicity law for the fixed-resolution screen audit cost/kernel rank package. -/
def fixedResolutionScreenMonotone (m n : ℕ) : Prop :=
  ∀ c' : ℕ,
    0 < c' → c' ≤ fixedResolutionScreenComponents m n →
      c' - 1 ≤ fixedResolutionScreenKernelRank m n

/-- Supermodularity law for the corank-style audit gap attached to a bounded rank function. -/
def fixedResolutionScreenSupermodular {V : Type*} [DecidableEq V] (ρ : ℕ)
    (r : Finset V → ℕ) : Prop :=
  ∀ s t,
    Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r s +
        Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r t ≤
      Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r (s ∩ t) +
        Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r (s ∪ t)

/-- Adding one face can reduce the connected-component count by at most one. -/
def fixedResolutionScreenUnitStep (m n : ℕ) : Prop :=
  ∀ c_after : ℕ,
    fixedResolutionScreenComponents m n - 1 ≤ c_after →
      c_after ≤ fixedResolutionScreenComponents m n →
        fixedResolutionScreenComponents m n - c_after ≤ 1

/-- Paper-facing fixed-resolution screen package: audit cost equals corank, the relative-homology
rank matches the kernel rank, connected components are counted by adding back the pinned exterior
component, the cost law is monotone, the corank audit gap is supermodular, and each added face
changes the cost by at most one step.
    thm:conclusion-fixedresolution-screen-corank-audit-cost-law -/
theorem paper_conclusion_fixedresolution_screen_corank_audit_cost_law
    {V : Type*} [DecidableEq V] (m n ρ : ℕ) (r : Finset V → ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hρ : ∀ s, r s ≤ ρ) (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    fixedResolutionScreenAuditCost m n = fixedResolutionScreenKernelRank m n ∧
      fixedResolutionScreenKernelRank m n = fixedResolutionScreenHomologyRank m n ∧
      fixedResolutionScreenHomologyRank m n + 1 = fixedResolutionScreenComponents m n ∧
      fixedResolutionScreenMonotone m n ∧
      fixedResolutionScreenSupermodular ρ r ∧
      fixedResolutionScreenUnitStep m n := by
  let _ := hm
  let _ := hn
  have hcomp_pos : 0 < fixedResolutionScreenComponents m n := by
    simp [fixedResolutionScreenComponents]
  have hcomp_one : 1 ≤ fixedResolutionScreenComponents m n := by
    omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Omega.SPG.ScreenKernelConnectedComponents.relative_homology_trivial_boundary
      (fixedResolutionScreenKernelRank m n)).symm
  · simpa [fixedResolutionScreenHomologyRank, fixedResolutionScreenKernelRank]
      using Omega.SPG.ScreenKernelConnectedComponents.free_components_count
        (fixedResolutionScreenComponents m n) hcomp_one
  · intro c' hc' hle
    simpa [fixedResolutionScreenKernelRank] using
      Omega.SPG.ScreenKernelConnectedComponents.screen_monotone_kernel
        (fixedResolutionScreenComponents m n) c' hcomp_pos hc' hle
  · intro s t
    exact Omega.Conclusion.ScreenAuditGapSupermodularity.auditGap_supermodular
      ρ r hρ hsub s t
  · intro c_after hbefore hafter
    simpa using Omega.SPG.ScreenKernelConnectedComponents.add_face_components_drop
      (fixedResolutionScreenComponents m n) c_after ⟨hbefore, hafter⟩

end Omega.Conclusion
