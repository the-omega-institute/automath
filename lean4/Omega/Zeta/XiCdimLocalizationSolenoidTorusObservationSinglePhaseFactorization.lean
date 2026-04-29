import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.Zeta

open scoped BigOperators

/-- The standard basis vector in `ℤ^n`. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis {n : ℕ}
    (i : Fin n) : Fin n → ℤ :=
  fun j => if j = i then 1 else 0

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_sum_zsmul_stdBasis
    {n : ℕ} (x : Fin n → ℤ) :
    ∑ i : Fin n,
        x i •
          xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis i = x := by
  funext j
  simp [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis]

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_map_eq_sum_basis
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (x : Fin n → ℤ) :
    ψ x =
      ∑ i : Fin n,
        x i •
          ψ
            (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis
              i) := by
  calc
    ψ x =
        ψ
          (∑ i : Fin n,
            x i •
              xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis
                i) := by
          rw [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_sum_zsmul_stdBasis]
    _ = ∑ i : Fin n,
          ψ
            (x i •
              xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis
                i) := by
          rw [map_sum]
    _ = ∑ i : Fin n,
          x i •
            ψ
              (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis
                i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using ψ.map_zsmul
            (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis i)
            (x i)

/-- The denominator of the `i`-th dual basis image. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (i : Fin n) : ℚ :=
  ((ψ
      (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis i) :
        SupportedLocalizedIntegerGroup S) : ℚ)

/-- The denominator of the `i`-th dual basis image. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (i : Fin n) : Nat :=
  (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue ψ i).den

/-- The common period obtained by multiplying the basis denominators. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) : Nat :=
  ∏ i : Fin n,
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ i

/-- The minimal prime-support subset detected by the observation, defined from the common period. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) : Finset Nat :=
  (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ).primeFactors

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen_pos
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (i : Fin n) :
    0 <
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ i := by
  dsimp [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen]
  exact Rat.den_pos _

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period_pos
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) :
    0 < xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ := by
  unfold xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period
  refine Finset.prod_pos ?_
  intro i hi
  exact xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen_pos ψ i

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period_ne_zero
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) :
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ ≠ 0 :=
  Nat.ne_of_gt
    (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period_pos ψ)

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen_dvd_period
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (i : Fin n) :
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ i ∣
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ := by
  unfold xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period
  exact Finset.dvd_prod_of_mem
    (fun j =>
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ j)
    (Finset.mem_univ i)

/-- The integer weight of the `i`-th basis direction relative to the common scalar
`1 / period(ψ)`. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (i : Fin n) : ℤ :=
  ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue ψ i).num) *
    ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ /
        xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ i :
      Nat) : ℤ)

/-- The single integer phase extracted from a torus observation. -/
def xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_phase
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (x : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n,
    x i *
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight ψ i

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_scalar_supported
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) :
    denominatorSupportedBy
      (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ)
      ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ : ℚ)⁻¹) := by
  intro p hp hdiv
  have hden :
      ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ : ℚ)⁻¹).den =
        xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ := by
    simpa using Rat.inv_natCast_den_of_pos
      (a := xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ)
      (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period_pos ψ)
  have hp_mem :
      p ∈
        (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ).primeFactors := by
    exact Nat.mem_primeFactors.mpr
      ⟨hp, by simpa [hden] using hdiv,
        xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period_ne_zero ψ⟩
  simpa [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support] using hp_mem

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basis_value
    {S : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (i : Fin n) :
    (((ψ
          (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis i) :
            SupportedLocalizedIntegerGroup S) : ℚ)) =
      (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight ψ i : ℤ) :
          ℚ) *
        ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ : ℚ)⁻¹)) := by
  let q : ℚ :=
    ((ψ
        (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis i) :
          SupportedLocalizedIntegerGroup S) : ℚ)
  let d : Nat :=
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ i
  let N : Nat := xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ
  let m : Nat := N / d
  have hd : d ∣ N :=
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen_dvd_period ψ i
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero q
  have hNq : (N : ℚ) ≠ 0 := by
    exact_mod_cast
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period_ne_zero ψ
  have hNm : d * m = N := by
    simpa [m] using Nat.mul_div_cancel' hd
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
    _ = (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight ψ i :
            ℤ) : ℚ) *
          ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
            ℚ)⁻¹)) := by
          dsimp [q, d, N, m,
            xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight,
            xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue,
            xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period,
            xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen]

private lemma xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support_minimal
    {S T : Finset Nat} {n : ℕ}
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S)
    (hT :
      ∀ i : Fin n,
        denominatorSupportedBy T
          (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue ψ i)) :
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ ⊆ T := by
  intro p hp
  have hp' :
      p ∈
        (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ).primeFactors := by
    simpa [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support] using hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp'
  have hp_dvd_period :
      p ∣ xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :=
    Nat.dvd_of_mem_primeFactors hp'
  rcases (hp_prime.prime.dvd_finset_prod_iff
      (fun i : Fin n =>
        xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen ψ i)).mp
      hp_dvd_period with ⟨i, -, hp_dvd_basis⟩
  exact hT i p hp_prime <| by
    simpa [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisDen] using
      hp_dvd_basis

/-- Paper label: `thm:xi-cdim-localization-solenoid-torus-observation-single-phase-factorization`.
On the Pontryagin-dual side, every finite-rank torus observation `ℤ^n → G_S` is controlled by the
single period obtained from the denominators of the basis images, so the whole map factors through
one integer phase and the induced prime support is the minimal one compatible with those basis
values. -/
theorem paper_xi_cdim_localization_solenoid_torus_observation_single_phase_factorization
    (S : Finset Nat) (n : ℕ)
    (ψ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) :
    xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ ⊆ S ∧
      denominatorSupportedBy
        (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ)
        ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ : ℚ)⁻¹) ∧
      (∀ x : Fin n → ℤ,
        (ψ x : ℚ) =
          (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_phase ψ x :
                ℤ) : ℚ) *
            ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
              ℚ)⁻¹))) ∧
      (∀ T : Finset Nat,
        (∀ i : Fin n,
          denominatorSupportedBy T
            (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue ψ i)) →
          xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ ⊆ T) := by
  refine ⟨?_, xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_scalar_supported
    ψ, ?_, ?_⟩
  · exact
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support_minimal ψ
        (fun i => (ψ
          (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_stdBasis i)).2)
  · intro x
    have hx :
        (ψ x : ℚ) =
          ∑ i : Fin n,
            (x i : ℚ) *
              xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue ψ i := by
      simpa [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue,
        zsmul_eq_mul] using congrArg
        (fun y : SupportedLocalizedIntegerGroup S => (y : ℚ))
        (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_map_eq_sum_basis
          ψ x)
    rw [hx]
    calc
      ∑ i : Fin n,
          (x i : ℚ) *
            xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue ψ i
          =
        ∑ i : Fin n,
          (x i : ℚ) *
            (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight ψ i :
                  ℤ) : ℚ) *
              ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
                ℚ)⁻¹)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact congrArg (fun t : ℚ => (x i : ℚ) * t) <|
                by
                  simpa
                    [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basisValue]
                    using
                      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_basis_value
                        ψ i
      _ =
        (∑ i : Fin n,
          ((x i *
                xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight ψ i :
                ℤ) : ℚ)) *
          ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
            ℚ)⁻¹) := by
              calc
                ∑ i : Fin n,
                    (x i : ℚ) *
                      (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight
                              ψ i :
                            ℤ) : ℚ) *
                        ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period
                              ψ :
                            ℚ)⁻¹))
                    =
                  ∑ i : Fin n,
                    (((x i *
                          xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight
                              ψ i :
                          ℤ) : ℚ) *
                      ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period
                            ψ :
                          ℚ)⁻¹)) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        norm_num [mul_assoc, mul_left_comm, mul_comm]
                _ =
                  (∑ i : Fin n,
                    ((x i *
                          xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_weight
                              ψ i :
                          ℤ) : ℚ)) *
                    ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
                      ℚ)⁻¹) := by
                        rw [Finset.sum_mul]
      _ =
        (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_phase ψ x :
              ℤ) : ℚ) *
          ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
            ℚ)⁻¹)) := by
              simp [xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_phase]
  · intro T hT
    exact
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support_minimal ψ hT

end Omega.Zeta
