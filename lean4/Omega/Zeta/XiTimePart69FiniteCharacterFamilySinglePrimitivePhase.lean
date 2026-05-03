import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.Zeta

open scoped BigOperators

/-- The denominator of the `i`-th member of a finite localized-integer family. -/
def xi_time_part69_finite_character_family_single_primitive_phase_den
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S)
    (i : Fin r) : Nat :=
  (χ i).1.den

/-- A common denominator for the finite family, obtained by multiplying all denominators. -/
def xi_time_part69_finite_character_family_single_primitive_phase_period
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S) : Nat :=
  ∏ i : Fin r, xi_time_part69_finite_character_family_single_primitive_phase_den χ i

private lemma xi_time_part69_finite_character_family_single_primitive_phase_den_pos
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S)
    (i : Fin r) :
    0 < xi_time_part69_finite_character_family_single_primitive_phase_den χ i := by
  dsimp [xi_time_part69_finite_character_family_single_primitive_phase_den]
  exact Rat.den_pos _

private lemma xi_time_part69_finite_character_family_single_primitive_phase_period_pos
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S) :
    0 < xi_time_part69_finite_character_family_single_primitive_phase_period χ := by
  unfold xi_time_part69_finite_character_family_single_primitive_phase_period
  refine Finset.prod_pos ?_
  intro i hi
  exact xi_time_part69_finite_character_family_single_primitive_phase_den_pos χ i

private lemma xi_time_part69_finite_character_family_single_primitive_phase_period_ne_zero
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S) :
    xi_time_part69_finite_character_family_single_primitive_phase_period χ ≠ 0 :=
  Nat.ne_of_gt (xi_time_part69_finite_character_family_single_primitive_phase_period_pos χ)

private lemma xi_time_part69_finite_character_family_single_primitive_phase_den_dvd_period
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S)
    (i : Fin r) :
    xi_time_part69_finite_character_family_single_primitive_phase_den χ i ∣
      xi_time_part69_finite_character_family_single_primitive_phase_period χ := by
  unfold xi_time_part69_finite_character_family_single_primitive_phase_period
  exact Finset.dvd_prod_of_mem
    (fun j => xi_time_part69_finite_character_family_single_primitive_phase_den χ j)
    (Finset.mem_univ i)

/-- Integer numerator of `χ i` after clearing the common denominator. -/
def xi_time_part69_finite_character_family_single_primitive_phase_weight
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S)
    (i : Fin r) : ℤ :=
  (χ i).1.num *
    ((xi_time_part69_finite_character_family_single_primitive_phase_period χ /
        xi_time_part69_finite_character_family_single_primitive_phase_den χ i : Nat) : ℤ)

private lemma xi_time_part69_finite_character_family_single_primitive_phase_inv_period_supported
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S) :
    denominatorSupportedBy S
      ((xi_time_part69_finite_character_family_single_primitive_phase_period χ : ℚ)⁻¹) := by
  intro p hp hdiv
  have hden :
      ((xi_time_part69_finite_character_family_single_primitive_phase_period χ : ℚ)⁻¹).den =
        xi_time_part69_finite_character_family_single_primitive_phase_period χ := by
    simpa using Rat.inv_natCast_den_of_pos
      (a := xi_time_part69_finite_character_family_single_primitive_phase_period χ)
      (xi_time_part69_finite_character_family_single_primitive_phase_period_pos χ)
  have hp_dvd_period :
      p ∣ xi_time_part69_finite_character_family_single_primitive_phase_period χ := by
    simpa [hden] using hdiv
  rcases (hp.prime.dvd_finset_prod_iff
      (fun i : Fin r =>
        xi_time_part69_finite_character_family_single_primitive_phase_den χ i)).mp
      hp_dvd_period with ⟨i, -, hp_dvd_den⟩
  exact (χ i).2 p hp <| by
    simpa [xi_time_part69_finite_character_family_single_primitive_phase_den] using hp_dvd_den

/-- The common localized phase `1 / period`. -/
def xi_time_part69_finite_character_family_single_primitive_phase_common_phase
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S) :
    SupportedLocalizedIntegerGroup S :=
  ⟨(xi_time_part69_finite_character_family_single_primitive_phase_period χ : ℚ)⁻¹,
    xi_time_part69_finite_character_family_single_primitive_phase_inv_period_supported χ⟩

private lemma xi_time_part69_finite_character_family_single_primitive_phase_value_eq_weight
    {S : Finset Nat} {r : Nat} (χ : Fin r → SupportedLocalizedIntegerGroup S)
    (i : Fin r) :
    χ i =
      xi_time_part69_finite_character_family_single_primitive_phase_weight χ i •
        xi_time_part69_finite_character_family_single_primitive_phase_common_phase χ := by
  ext
  let q : ℚ := (χ i).1
  let d : Nat := xi_time_part69_finite_character_family_single_primitive_phase_den χ i
  let N : Nat := xi_time_part69_finite_character_family_single_primitive_phase_period χ
  let m : Nat := N / d
  have hd : d ∣ N :=
    xi_time_part69_finite_character_family_single_primitive_phase_den_dvd_period χ i
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero q
  have hNq : (N : ℚ) ≠ 0 := by
    exact_mod_cast xi_time_part69_finite_character_family_single_primitive_phase_period_ne_zero χ
  have hNm : d * m = N := by
    simpa [m] using Nat.mul_div_cancel' hd
  change q =
    ((xi_time_part69_finite_character_family_single_primitive_phase_weight χ i : ℤ) : ℚ) *
      ((N : ℚ)⁻¹)
  calc
    q = (q.num : ℚ) / q.den := by simpa using (Rat.num_div_den q).symm
    _ = (q.num : ℚ) / d := by rfl
    _ = (((q.num * (m : ℤ)) : ℤ) : ℚ) / N := by
      apply (div_eq_div_iff hdq hNq).2
      have hNmq : (N : ℚ) = d * m := by exact_mod_cast hNm.symm
      rw [hNmq]
      norm_num [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = (((q.num * (m : ℤ)) : ℤ) : ℚ) * ((N : ℚ)⁻¹) := by
      rw [div_eq_mul_inv]
    _ =
      ((xi_time_part69_finite_character_family_single_primitive_phase_weight χ i : ℤ) : ℚ) *
        ((N : ℚ)⁻¹) := by
      dsimp [q, d, N, m, xi_time_part69_finite_character_family_single_primitive_phase_weight,
        xi_time_part69_finite_character_family_single_primitive_phase_den]

/-- Primitive coefficient condition: after extracting the finite-family gcd, the residual
coefficients have gcd `1`; for the empty family the condition is vacuous. -/
def xi_time_part69_finite_character_family_single_primitive_phase_primitive_gcd_up_to_sign
    {r : Nat} (coeff : Fin r → ℤ) : Prop :=
  r = 0 ∨ (Finset.univ.gcd coeff = (1 : ℤ))

/-- Concrete statement for the finite localized-character family: all members are integer
multiples of one localized phase, and the integer coefficients are primitive up to sign. -/
def xi_time_part69_finite_character_family_single_primitive_phase_statement
    (S : Finset Nat) (r : Nat) (χ : Fin r → SupportedLocalizedIntegerGroup S) : Prop :=
  ∃ phase : SupportedLocalizedIntegerGroup S, ∃ coeff : Fin r → ℤ,
    (∀ i : Fin r, χ i = coeff i • phase) ∧
      xi_time_part69_finite_character_family_single_primitive_phase_primitive_gcd_up_to_sign coeff

/-- Paper label: `thm:xi-time-part69-finite-character-family-single-primitive-phase`. -/
theorem paper_xi_time_part69_finite_character_family_single_primitive_phase
    (S : Finset Nat) (r : Nat) (χ : Fin r → SupportedLocalizedIntegerGroup S) :
    xi_time_part69_finite_character_family_single_primitive_phase_statement S r χ := by
  by_cases hr : r = 0
  · refine ⟨localizedOne S, fun i : Fin r => 0, ?_, Or.inl hr⟩
    intro i
    exact False.elim (Fin.elim0 (hr ▸ i))
  · have hpos : 0 < r := Nat.pos_of_ne_zero hr
    have huniv : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
    obtain ⟨coeff, hcoeff, hcoeff_gcd⟩ :=
      Finset.extract_gcd
        (s := (Finset.univ : Finset (Fin r)))
        (f := xi_time_part69_finite_character_family_single_primitive_phase_weight χ) huniv
    refine
      ⟨(Finset.univ.gcd
            (xi_time_part69_finite_character_family_single_primitive_phase_weight χ)) •
          xi_time_part69_finite_character_family_single_primitive_phase_common_phase χ,
        coeff, ?_, Or.inr hcoeff_gcd⟩
    intro i
    calc
      χ i =
          xi_time_part69_finite_character_family_single_primitive_phase_weight χ i •
            xi_time_part69_finite_character_family_single_primitive_phase_common_phase χ :=
        xi_time_part69_finite_character_family_single_primitive_phase_value_eq_weight χ i
      _ =
          ((Finset.univ.gcd
              (xi_time_part69_finite_character_family_single_primitive_phase_weight χ)) *
              coeff i) •
            xi_time_part69_finite_character_family_single_primitive_phase_common_phase χ := by
        rw [hcoeff i (Finset.mem_univ i)]
      _ =
          coeff i •
            ((Finset.univ.gcd
                (xi_time_part69_finite_character_family_single_primitive_phase_weight χ)) •
              xi_time_part69_finite_character_family_single_primitive_phase_common_phase χ) := by
        rw [mul_comm, smul_smul]

end Omega.Zeta
