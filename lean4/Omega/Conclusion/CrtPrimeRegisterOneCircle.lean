import Mathlib.Data.Nat.Basic

namespace Omega

/-- Concrete prime-register data for the CRT one-circle law: each prime has a finite
    quotient dimension and `pcdim` records the resulting prime-register circle dimension. -/
structure conclusion_crt_prime_register_one_circle_Data where
  pPrimaryQuotientDim : ℕ → ℕ
  pcdim : ℕ

/-- The pro-cyclic prime-register bound on all prime-primary quotients. -/
def conclusion_crt_prime_register_one_circle_dp_bound
    (K : conclusion_crt_prime_register_one_circle_Data) : Prop :=
  ∀ p, K.pPrimaryQuotientDim p ≤ 1

/-- A nontrivial infinite prime component is represented by a prime direction of dimension one. -/
def conclusion_crt_prime_register_one_circle_Data.hasInfinitePComponent
    (K : conclusion_crt_prime_register_one_circle_Data) : Prop :=
  ∃ p, K.pPrimaryQuotientDim p = 1

/-- The pro-cyclic interface: all prime quotients are at most one-dimensional, and `pcdim`
    is the maximum of those rank-one prime directions. -/
noncomputable def conclusion_crt_prime_register_one_circle_Data.procyclic
    (K : conclusion_crt_prime_register_one_circle_Data) : Prop :=
  by
    classical
    exact conclusion_crt_prime_register_one_circle_dp_bound K ∧
      K.pcdim = if K.hasInfinitePComponent then 1 else 0

/-- A one-circle phase extension is modeled by a unit-circle parameter space, together with
    the rank-one prime-register dimension forced by a nontrivial infinite component. -/
def conclusion_crt_prime_register_one_circle_Data.phaseExtension
    (K : conclusion_crt_prime_register_one_circle_Data) (S : Type) : Prop :=
  Nonempty S ∧ K.pcdim = 1

/-- Paper wrapper for the CRT prime-register one-circle law.
    cor:conclusion-crt-prime-register-one-circle -/
theorem paper_conclusion_crt_prime_register_one_circle
    (K : conclusion_crt_prime_register_one_circle_Data) (hcyc : K.procyclic) :
    conclusion_crt_prime_register_one_circle_dp_bound K ∧ K.pcdim ≤ 1 ∧
      (K.hasInfinitePComponent → K.pcdim = 1) ∧
      (K.hasInfinitePComponent → ∃ S : Type, K.phaseExtension S) := by
  rcases hcyc with ⟨hbound, hpcdim⟩
  refine ⟨hbound, ?_, ?_, ?_⟩
  · rw [hpcdim]
    by_cases h : K.hasInfinitePComponent <;> simp [h]
  · intro h
    rw [hpcdim]
    simp [h]
  · intro h
    refine ⟨PUnit, ⟨⟨PUnit.unit⟩, ?_⟩⟩
    rw [hpcdim]
    simp [h]

end Omega
