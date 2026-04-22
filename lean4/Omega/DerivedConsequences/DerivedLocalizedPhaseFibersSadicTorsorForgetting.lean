import Omega.CircleDimension.LissajousMinimalSolenoidFactor
import Omega.CircleDimension.SolenoidFiberTorsor

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-localized-phase-fibers-sadic-torsor-forgetting`. -/
theorem paper_derived_localized_phase_fibers_sadic_torsor_forgetting (S : Finset ℕ) :
    Nonempty (Omega.CircleDimension.SolenoidProjectionKernel S ≃
      Omega.CircleDimension.SolenoidKernelProductZpModel S) ∧
    (∀ {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G),
      f x = f y → ∃! k : G, k ∈ f.ker ∧ y = x * k) := by
  exact ⟨(Omega.CircleDimension.paper_cdim_solenoid_kernel_product_zp S).2,
    Omega.CircleDimension.paper_cdim_solenoid_fiber_torsor.2.2.1⟩

