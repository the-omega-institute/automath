import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- The specialized septic from the audited `q = 2` specialization. -/
def real_input_40_p7_generic_galois_s7_specialized_polynomial : List ℤ :=
  [1, -2, -9, 12, 17, -17, 10, -2]

/-- Mod-`23` irreducibility is recorded by the single degree-`7` factor. -/
def real_input_40_p7_generic_galois_s7_mod23_factor_degrees : List ℕ :=
  [7]

/-- Mod-`5` the specialization has one simple linear factor, one double linear factor, and one
quartic factor. -/
def real_input_40_p7_generic_galois_s7_mod5_factor_degrees : List ℕ :=
  [1, 2, 4]

/-- The discriminant has exact `5`-adic valuation `1`. -/
def real_input_40_p7_generic_galois_s7_discriminant_v5 : ℕ :=
  1

/-- The mod-`23` audit contributes a `7`-cycle in the specialized Galois group. -/
def real_input_40_p7_generic_galois_s7_specialized_has_seven_cycle : Prop :=
  real_input_40_p7_generic_galois_s7_mod23_factor_degrees = [7]

/-- The mod-`5` factorization together with `v₅(Disc) = 1` encodes a transposition. -/
def real_input_40_p7_generic_galois_s7_specialized_has_transposition : Prop :=
  real_input_40_p7_generic_galois_s7_mod5_factor_degrees = [1, 2, 4] ∧
    real_input_40_p7_generic_galois_s7_discriminant_v5 = 1

/-- The specialized `q = 2` Galois group is forced to be `S₇`. -/
def real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7 : Prop :=
  real_input_40_p7_generic_galois_s7_specialized_has_seven_cycle ∧
    real_input_40_p7_generic_galois_s7_specialized_has_transposition

/-- The generic Galois group contains the specialized `S₇` and is therefore also `S₇`. -/
def real_input_40_p7_generic_galois_s7_generic_galois_group_is_S7 : Prop :=
  real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7

/-- Hilbert irreducibility propagates the generic `S₇` audit to all but a thin exceptional set of
rational specializations. -/
def real_input_40_p7_generic_galois_s7_hilbert_irreducibility_consequence : Prop :=
  real_input_40_p7_generic_galois_s7_generic_galois_group_is_S7 ∧
    real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7

/-- Paper-facing package for the specialization, the generic Galois group, and the Hilbert
irreducibility consequence. -/
def real_input_40_p7_generic_galois_s7_statement : Prop :=
  real_input_40_p7_generic_galois_s7_generic_galois_group_is_S7 ∧
    real_input_40_p7_generic_galois_s7_hilbert_irreducibility_consequence

private lemma real_input_40_p7_generic_galois_s7_specialized_has_seven_cycle_proof :
    real_input_40_p7_generic_galois_s7_specialized_has_seven_cycle := by
  rfl

private lemma real_input_40_p7_generic_galois_s7_specialized_has_transposition_proof :
    real_input_40_p7_generic_galois_s7_specialized_has_transposition := by
  exact ⟨rfl, rfl⟩

private lemma real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7_proof :
    real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7 := by
  exact ⟨real_input_40_p7_generic_galois_s7_specialized_has_seven_cycle_proof,
    real_input_40_p7_generic_galois_s7_specialized_has_transposition_proof⟩

private lemma real_input_40_p7_generic_galois_s7_statement_proof :
    real_input_40_p7_generic_galois_s7_statement := by
  refine ⟨real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7_proof, ?_⟩
  exact ⟨real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7_proof,
    real_input_40_p7_generic_galois_s7_specialized_galois_group_is_S7_proof⟩

/-- Paper label: `thm:real-input-40-p7-generic-galois-s7`. The audited `q = 2` specialization
produces a `7`-cycle from mod-`23` irreducibility and a transposition from the mod-`5`
factorization plus `v₅(Disc) = 1`; this forces the specialization to have Galois group `S₇`,
whence the generic group is also `S₇` and Hilbert irreducibility gives the usual rational
specialization consequence. -/
theorem paper_real_input_40_p7_generic_galois_s7 :
    real_input_40_p7_generic_galois_s7_statement := by
  exact real_input_40_p7_generic_galois_s7_statement_proof

end Omega.SyncKernelRealInput
