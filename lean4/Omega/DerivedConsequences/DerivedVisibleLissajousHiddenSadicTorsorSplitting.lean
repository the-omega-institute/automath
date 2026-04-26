import Mathlib.Tactic
import Omega.CircleDimension.LissajousMinimalSolenoidFactor
import Omega.CircleDimension.LissajousPhaseCirclePrimeLedgerKernel
import Omega.CircleDimension.SolenoidFiberTorsor
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.DerivedConsequences

/-- Paper-facing visible/hidden splitting package for the two-prime Lissajous lift. -/
def derived_visible_lissajous_hidden_sadic_torsor_splitting_statement
    (a b p q : ℕ) (δ : ℝ) : Prop :=
  let S : Finset ℕ := {p, q}
  Omega.CircleDimension.LissajousMinimalSolenoidFactorStatement a b ∧
    Nonempty (Omega.CircleDimension.SolenoidProjectionKernel S ≃
      Omega.CircleDimension.SolenoidKernelProductZpModel S) ∧
    (∀ {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G),
      f x = f y → ∃! k : G, k ∈ f.ker ∧ y = x * k) ∧
    ∀ t : ℝ,
      Omega.CircleDimension.lissajousVisibleOrbit a b δ t =
        Omega.CircleDimension.phaseJoukowskyPair
          (Omega.CircleDimension.lissajousPhaseLift a b δ t)

/-- Paper label: `cor:derived-visible-lissajous-hidden-sadic-torsor-splitting`. -/
theorem paper_derived_visible_lissajous_hidden_sadic_torsor_splitting
    (a b p q : ℕ) (δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    derived_visible_lissajous_hidden_sadic_torsor_splitting_statement a b p q δ := by
  dsimp [derived_visible_lissajous_hidden_sadic_torsor_splitting_statement]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Omega.CircleDimension.paper_cdim_lissajous_minimal_solenoid_factor a b ha hb
  · exact (Omega.CircleDimension.paper_cdim_solenoid_kernel_product_zp ({p, q} : Finset ℕ)).2
  · intro G H _ _ f x y hxy
    exact Omega.CircleDimension.fiber_torsor_unique f x y hxy
  · intro t
    rfl

end Omega.DerivedConsequences
