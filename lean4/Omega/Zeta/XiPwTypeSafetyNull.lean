import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelRankMinimalLinearRealization

namespace Omega.Zeta

/-- Concrete read-visible symmetry data: a state space together with its visible readout. -/
structure ReadVisibleSymmetryData (Omega Y : Type*) [DecidableEq Omega] where
  read : Omega → Y

/-- A permutation is a read symmetry when it preserves the visible readout on every state. -/
def ReadVisibleSymmetryData.isReadSymmetry
    {Omega Y : Type*} [DecidableEq Omega]
    (D : ReadVisibleSymmetryData Omega Y) (σ : Equiv.Perm Omega) : Prop :=
  ∀ omega : Omega, D.read (σ omega) = D.read omega

/-- The orbit of a state under all read-preserving permutations. -/
def ReadVisibleSymmetryData.readOrbit
    {Omega Y : Type*} [DecidableEq Omega]
    (D : ReadVisibleSymmetryData Omega Y) (omega : Omega) : Set Omega :=
  {omega' | ∃ σ : Equiv.Perm Omega, D.isReadSymmetry σ ∧ σ omega = omega'}

/-- The read-preserving orbit of a state is exactly its read fiber.
    prop:xi-read-fiber-orbits -/
theorem paper_xi_read_fiber_orbits
    {Omega Y : Type*} [DecidableEq Omega]
    (D : ReadVisibleSymmetryData Omega Y) (omega : Omega) :
    D.readOrbit omega = {omega' | D.read omega' = D.read omega} := by
  ext omega'
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hσ omega
  · intro hread
    refine ⟨Equiv.swap omega omega', ?_, ?_⟩
    · intro x
      by_cases hx : x = omega
      · subst hx
        simpa [Equiv.swap_apply_left] using hread
      · by_cases hx' : x = omega'
        · subst hx'
          simpa [Equiv.swap_apply_right] using hread.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
    · simp [Equiv.swap_apply_left]

open HankelMaximalMinorSyndromeData

/-- Concrete audit data for the PW-type-safety `NULL` criterion on the mode axis.  Each layer and
phase sample comes with an explicit Hankel witness, a required visible mode count, and the
protocol-level `NULL` output produced when a chosen mode budget is too small. -/
structure XiPwTypeSafetyNullData where
  Layer : Type
  Phase : Type
  k : Type
  field_k : Field k
  witness : Layer → Phase → HankelMaximalMinorSyndromeData k
  requiredModeDim : Layer → Phase → ℕ
  nullReadout : ℕ → Layer → Phase → Prop
  uniformMinimality : ∀ ℓ θ, requiredModeDim ℓ θ = (witness ℓ θ).d
  protocolClosure : ∀ d ℓ θ, d < requiredModeDim ℓ θ → nullReadout d ℓ θ
  recordedModesSuffice : ∀ d ℓ θ, requiredModeDim ℓ θ ≤ d → ¬ nullReadout d ℓ θ

attribute [instance] XiPwTypeSafetyNullData.field_k

namespace XiPwTypeSafetyNullData

/-- A single finite mode budget works uniformly, so no layer/phase sample is rejected as `NULL`
for needing an unrecorded extra visible mode. -/
def modeAxisCompleteness (D : XiPwTypeSafetyNullData) : Prop :=
  ∃ d : ℕ, ∀ ℓ θ, ¬ D.nullReadout d ℓ θ

/-- The Hankel witnesses have a uniform rank bound across all layers and phase samples. -/
def hankelRanksUniformlyBounded (D : XiPwTypeSafetyNullData) : Prop :=
  ∃ d : ℕ, ∀ ℓ θ, (D.witness ℓ θ).d ≤ d

end XiPwTypeSafetyNullData

/-- Under uniform minimality and protocol closure, a uniform bound on the Hankel ranks is exactly
the condition that prevents the PW protocol from producing a dimension-forced `NULL` because an
unrecorded extra visible mode would be needed.
    thm:xi-completeness-iff-hankel-bounded -/
theorem paper_xi_completeness_iff_hankel_bounded (D : XiPwTypeSafetyNullData) :
    D.modeAxisCompleteness ↔ D.hankelRanksUniformlyBounded := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro ℓ θ
    by_contra hlt
    have hreq : d < D.requiredModeDim ℓ θ := by
      rw [D.uniformMinimality ℓ θ]
      exact lt_of_not_ge hlt
    have hnull : D.nullReadout d ℓ θ := D.protocolClosure d ℓ θ hreq
    exact hd ℓ θ hnull
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro ℓ θ
    have _ := paper_xi_hankel_rank_minimal_linear_realization (D.witness ℓ θ)
    have hreq : D.requiredModeDim ℓ θ ≤ d := by
      rw [D.uniformMinimality ℓ θ]
      exact hd ℓ θ
    exact D.recordedModesSuffice d ℓ θ hreq

end Omega.Zeta
