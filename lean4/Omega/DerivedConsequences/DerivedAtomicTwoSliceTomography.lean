import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.DerivedConsequences

noncomputable section

/-- Fixed three-modulus CRT seed used to model the residue reconstruction step in the paper proof.
The coefficients `15`, `10`, and `6` are the standard idempotents for the pairwise coprime moduli
`2`, `3`, and `5`. -/
def derived_atomic_two_slice_tomography_crt_reconstruct (l2 l3 l5 : ℕ) : ℕ :=
  (15 * l2 + 10 * l3 + 6 * l5) % 30

/-- Single-slice coefficient model `c = m u^E`. -/
noncomputable def derived_atomic_two_slice_tomography_slice_coeff (u m E : ℝ) : ℝ :=
  m * u ^ E

/-- Concrete fixed-modulus seed for the two-slice tomography argument. -/
def derived_atomic_two_slice_tomography_statement : Prop :=
  ∀ ℓ : ℕ,
    ℓ < 30 →
    ∀ u₁ u₂ m E : ℝ,
      0 < u₁ →
      0 < u₂ →
      u₁ ≠ u₂ →
      0 < m →
        derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) = ℓ ∧
          Real.log
              (derived_atomic_two_slice_tomography_slice_coeff u₂ m E /
                derived_atomic_two_slice_tomography_slice_coeff u₁ m E) /
            Real.log (u₂ / u₁) = E ∧
          derived_atomic_two_slice_tomography_slice_coeff u₁ m E * u₁ ^ (-E) = m

lemma derived_atomic_two_slice_tomography_crt_reconstruct_lt (l2 l3 l5 : ℕ) :
    derived_atomic_two_slice_tomography_crt_reconstruct l2 l3 l5 < 30 := by
  dsimp [derived_atomic_two_slice_tomography_crt_reconstruct]
  exact Nat.mod_lt _ (by decide)

lemma derived_atomic_two_slice_tomography_crt_reconstruct_mod_two (ℓ : ℕ) :
    derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) ≡ ℓ [MOD 2] := by
  rw [Nat.ModEq, derived_atomic_two_slice_tomography_crt_reconstruct]
  omega

lemma derived_atomic_two_slice_tomography_crt_reconstruct_mod_three (ℓ : ℕ) :
    derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) ≡ ℓ [MOD 3] := by
  rw [Nat.ModEq, derived_atomic_two_slice_tomography_crt_reconstruct]
  omega

lemma derived_atomic_two_slice_tomography_crt_reconstruct_mod_five (ℓ : ℕ) :
    derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) ≡ ℓ [MOD 5] := by
  rw [Nat.ModEq, derived_atomic_two_slice_tomography_crt_reconstruct]
  omega

lemma derived_atomic_two_slice_tomography_crt_reconstruct_eq (ℓ : ℕ) (hℓ : ℓ < 30) :
    derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) = ℓ := by
  have hlt :
      derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) < 30 :=
    derived_atomic_two_slice_tomography_crt_reconstruct_lt _ _ _
  have hmod6 :
      derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) ≡ ℓ [MOD 2 * 3] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).1
      ⟨derived_atomic_two_slice_tomography_crt_reconstruct_mod_two ℓ,
        derived_atomic_two_slice_tomography_crt_reconstruct_mod_three ℓ⟩
  have hmod30 :
      derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) ≡
        ℓ [MOD (2 * 3) * 5] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime (2 * 3) 5 by decide)).1
      ⟨hmod6, derived_atomic_two_slice_tomography_crt_reconstruct_mod_five ℓ⟩
  have hmod30' :
      derived_atomic_two_slice_tomography_crt_reconstruct (ℓ % 2) (ℓ % 3) (ℓ % 5) ≡ ℓ [MOD 30] := by
    simpa using hmod30
  exact Nat.ModEq.eq_of_lt_of_lt hmod30' hlt hℓ

lemma derived_atomic_two_slice_tomography_slice_ratio
    {u₁ u₂ m E : ℝ} (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hm : 0 < m) :
    derived_atomic_two_slice_tomography_slice_coeff u₂ m E /
      derived_atomic_two_slice_tomography_slice_coeff u₁ m E =
        (u₂ / u₁) ^ E := by
  dsimp [derived_atomic_two_slice_tomography_slice_coeff]
  rw [mul_div_mul_left _ _ (show m ≠ 0 by linarith)]
  exact (Real.div_rpow hu₂.le hu₁.le E).symm

/-- Paper label: `thm:derived-atomic-two-slice-tomography`. For the fixed pairwise coprime moduli
`2`, `3`, and `5`, the residue data reconstructs the unique index `ℓ < 30`, and two positive
slice coefficients `m u₁^E`, `m u₂^E` with `u₁ ≠ u₂` recover `E` and `m` by the explicit ratio and
first-slice formulas. -/
theorem paper_derived_atomic_two_slice_tomography :
    derived_atomic_two_slice_tomography_statement := by
  intro ℓ hℓ u₁ u₂ m E hu₁ hu₂ hu12 hm
  refine ⟨derived_atomic_two_slice_tomography_crt_reconstruct_eq ℓ hℓ, ?_, ?_⟩
  · have hratio :
        derived_atomic_two_slice_tomography_slice_coeff u₂ m E /
            derived_atomic_two_slice_tomography_slice_coeff u₁ m E =
          (u₂ / u₁) ^ E :=
      derived_atomic_two_slice_tomography_slice_ratio hu₁ hu₂ hm
    have hratio_pos : 0 < u₂ / u₁ := by positivity
    have hlog :
        Real.log
            (derived_atomic_two_slice_tomography_slice_coeff u₂ m E /
              derived_atomic_two_slice_tomography_slice_coeff u₁ m E) =
          E * Real.log (u₂ / u₁) := by
      rw [hratio, Real.log_rpow hratio_pos]
    have hden_ne : Real.log (u₂ / u₁) ≠ 0 := by
      intro hzero
      have hratio_one : u₂ / u₁ = 1 :=
        Real.eq_one_of_pos_of_log_eq_zero hratio_pos hzero
      have hu_eq : u₂ = u₁ := by
        simpa using (div_eq_iff (show u₁ ≠ 0 by linarith)).mp hratio_one
      exact hu12 hu_eq.symm
    exact (div_eq_iff hden_ne).2 hlog
  · calc
      derived_atomic_two_slice_tomography_slice_coeff u₁ m E * u₁ ^ (-E) =
          m * (u₁ ^ E * u₁ ^ (-E)) := by
            dsimp [derived_atomic_two_slice_tomography_slice_coeff]
            ring
      _ = m * (u₁ ^ E * (u₁ ^ E)⁻¹) := by
            rw [Real.rpow_neg (le_of_lt hu₁)]
      _ = m := by
            have hu₁E_ne : u₁ ^ E ≠ 0 := by
              exact ne_of_gt (Real.rpow_pos_of_pos hu₁ E)
            field_simp [hu₁E_ne]

end

end Omega.DerivedConsequences
