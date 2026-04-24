import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit
import Omega.Zeta.XiCdimLocalizationSolenoidNoNontrivialTorusInput

namespace Omega.Zeta

/-- The standard basis vector in `ℤ^n`. -/
private def torusStdBasis {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  fun j => if j = i then 1 else 0

private lemma sum_zsmul_torusStdBasis {n : ℕ} (x : Fin n → ℤ) :
    ∑ i : Fin n, x i • torusStdBasis i = x := by
  funext j
  simp [torusStdBasis]

private lemma map_eq_sum_basis {S : Finset Nat} {n : ℕ}
    (φ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (x : Fin n → ℤ) :
    φ x = ∑ i : Fin n, x i • φ (torusStdBasis i) := by
  calc
    φ x = φ (∑ i : Fin n, x i • torusStdBasis i) := by
      rw [sum_zsmul_torusStdBasis]
    _ = ∑ i : Fin n, φ (x i • torusStdBasis i) := by
      rw [map_sum]
    _ = ∑ i : Fin n, x i • φ (torusStdBasis i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa using φ.map_zsmul (torusStdBasis i) (x i)

private lemma rat_den_sum_dvd_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℚ) :
    Rat.den (Finset.sum s q) ∣ Finset.prod s (fun i => Rat.den (q i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    have hadd : Rat.den (q a + Finset.sum s q) ∣ Rat.den (q a) * Rat.den (Finset.sum s q) :=
      Rat.add_den_dvd _ _
    have hadd' : Rat.den ((insert a s).sum q) ∣ Rat.den (q a) * Rat.den (Finset.sum s q) := by
      simpa [Finset.sum_insert ha] using hadd
    have hmul :
        Rat.den (q a) * Rat.den (Finset.sum s q) ∣
          Rat.den (q a) * Finset.prod s (fun i => Rat.den (q i)) :=
      Nat.mul_dvd_mul_left _ hs
    exact dvd_trans hadd' (by simpa [Finset.prod_insert ha] using hmul)

private lemma rat_den_intCast_mul_dvd (z : ℤ) (q : ℚ) :
    (((z : ℚ) * q).den) ∣ q.den := by
  simpa using (Rat.mul_den_dvd (z : ℚ) q)

private lemma localizedImage_den_dvd_basisProduct {S : Finset Nat} {n : ℕ}
    (φ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S) (x : Fin n → ℤ) :
    ((φ x : ℚ).den) ∣ Finset.prod Finset.univ fun i : Fin n => ((φ (torusStdBasis i) : ℚ).den) := by
  let q : Fin n → ℚ := fun i => (x i : ℚ) * (φ (torusStdBasis i) : ℚ)
  have hx :
      (φ x : ℚ) = ∑ i : Fin n, q i := by
    simpa [q, zsmul_eq_mul] using
      congrArg (fun y : SupportedLocalizedIntegerGroup S => (y : ℚ)) (map_eq_sum_basis φ x)
  rw [hx]
  refine dvd_trans (rat_den_sum_dvd_prod Finset.univ q) ?_
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
    rat_den_intCast_mul_dvd (x i) (φ (torusStdBasis i) : ℚ)

private lemma denominatorSupportedBy_inv_prime_pow {S : Finset Nat} {p k : Nat}
    (hpS : p ∈ S) (hp : p.Prime) : denominatorSupportedBy S ((p ^ k : ℚ)⁻¹) := by
  intro q hq hdiv
  by_cases hk : k = 0
  · subst hk
    have : q ∣ 1 := by
      simpa using hdiv
    exact False.elim (hq.not_dvd_one this)
  · have hden : (((p ^ k : ℚ)⁻¹).den) = p ^ k := by
      simpa [Nat.cast_pow] using Rat.inv_natCast_den_of_pos (a := p ^ k) (pow_pos hp.pos _)
    rw [hden] at hdiv
    have hqp : q ∣ p := hq.dvd_of_dvd_pow hdiv
    have hEq : q = p := by
      rcases (Nat.dvd_prime hp).mp hqp with hq1 | hqp'
      · exact False.elim (hq.ne_one hq1)
      · exact hqp'
    simpa [hEq] using hpS

private def localizedInvPrimePow (S : Finset Nat) (p k : Nat) (hpS : p ∈ S) (hp : p.Prime) :
    SupportedLocalizedIntegerGroup S :=
  ⟨(p ^ k : ℚ)⁻¹, denominatorSupportedBy_inv_prime_pow hpS hp⟩

private lemma localizedOne_eq_zsmul_invPrimePow (S : Finset Nat) (p k : Nat)
    (hpS : p ∈ S) (hp : p.Prime) :
    localizedOne S = (p ^ k : ℤ) • localizedInvPrimePow S p k hpS hp := by
  ext
  by_cases hk : k = 0
  · subst hk
    simp [localizedOne, localizedInvPrimePow]
  · have hkq : (p ^ k : ℚ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero k hp.ne_zero)
    change ((localizedOne S : SupportedLocalizedIntegerGroup S) : ℚ) =
      (((p ^ k : ℤ) • localizedInvPrimePow S p k hpS hp : SupportedLocalizedIntegerGroup S) : ℚ)
    simp [localizedOne, localizedInvPrimePow, zsmul_eq_mul, hkq]

private theorem int_eq_zero_of_dvd_all_powers {p : Nat} (hp : 2 ≤ p) {x : ℤ}
    (hdiv : ∀ n : Nat, ((p ^ n : ℕ) : ℤ) ∣ x) : x = 0 := by
  by_contra hx
  let n : Nat := Int.natAbs x + 1
  have hle : Int.natAbs (((p ^ n : ℕ) : ℤ)) ≤ Int.natAbs x :=
    Int.natAbs_le_of_dvd_ne_zero (hdiv n) hx
  have hlt_nat : Int.natAbs x < p ^ n := by
    have hlt_succ : Int.natAbs x < Int.natAbs x + 1 := by simp
    have hpow : n < p ^ n := by
      exact n.lt_pow_self (by omega)
    simpa [n] using lt_trans hlt_succ hpow
  have hlt : Int.natAbs x < Int.natAbs (((p ^ n : ℕ) : ℤ)) := by
    simpa using hlt_nat
  exact (not_lt_of_ge hle) hlt

private theorem vector_eq_zero_of_dvd_all_powers {p d : Nat} (hp : 2 ≤ p) {x : Fin d → ℤ}
    (hdiv : localizedSolenoidDualDivisibleAtPrime p x) : x = 0 := by
  ext i
  apply int_eq_zero_of_dvd_all_powers hp
  intro n
  rcases hdiv n with ⟨y, hy⟩
  refine ⟨y i, ?_⟩
  simpa [Pi.smul_apply, zsmul_eq_mul] using congrArg (fun f => f i) hy

/-- Dualized finite-torus obstruction for the localized solenoid: a finite torus embedding would
produce a surjection `ℤ^n ↠ G_S`, while a finite torus quotient would produce an injection
`G_S ↪ ℤ^n`. For every prime `p ∈ S`, both finite-rank models fail. -/
def XiCdimLocalizationSolenoidNotSubgroupOrQuotientOfFiniteTorus (S : Finset Nat) (n : ℕ) :
    Prop :=
  (∀ p, p.Prime → p ∈ S →
      ¬ ∃ φ : (Fin n → ℤ) →+ SupportedLocalizedIntegerGroup S, Function.Surjective φ) ∧
    (∀ p, p.Prime → p ∈ S →
      ¬ ∃ φ : SupportedLocalizedIntegerGroup S →+ (Fin n → ℤ), Function.Injective φ)

/-- Paper label: `thm:xi-cdim-localization-solenoid-not-subgroup-or-quotient-of-finite-torus`. -/
theorem paper_xi_cdim_localization_solenoid_not_subgroup_or_quotient_of_finite_torus
    (S : Finset Nat) (n : ℕ) (hn : 1 ≤ n) :
    XiCdimLocalizationSolenoidNotSubgroupOrQuotientOfFiniteTorus S n := by
  have _ := hn
  refine ⟨?_, ?_⟩
  · intro p hp hpS
    rintro ⟨φ, hsurj⟩
    let N : Nat := ∏ i : Fin n, ((φ (torusStdBasis i) : ℚ).den)
    let y : SupportedLocalizedIntegerGroup S := localizedInvPrimePow S p (N + 1) hpS hp
    rcases hsurj y with ⟨x, hx⟩
    have hdenBound := localizedImage_den_dvd_basisProduct φ x
    rw [hx] at hdenBound
    have hdiv : p ^ (N + 1) ∣ N := by
      simpa [N, y, localizedInvPrimePow, Nat.cast_pow, hp.ne_zero,
        Rat.inv_natCast_den_of_pos (a := p ^ (N + 1)) (pow_pos hp.pos _)] using hdenBound
    have hNpos : 0 < N := by
      unfold N
      refine Finset.prod_pos ?_
      intro i hi
      exact Rat.den_pos _
    have hlt : N < p ^ (N + 1) := by
      have hpow : N + 1 < p ^ (N + 1) := by
        exact (N + 1).lt_pow_self hp.two_le
      exact lt_trans (Nat.lt_succ_self N) hpow
    have hnot : ¬ p ^ (N + 1) ∣ N := by
      intro h
      have hge : p ^ (N + 1) ≤ N := Nat.le_of_dvd hNpos h
      exact (not_lt_of_ge hge) hlt
    exact hnot hdiv
  · intro p hp hpS
    rintro ⟨φ, hφinj⟩
    have hdiv : localizedSolenoidDualDivisibleAtPrime p (φ (localizedOne S)) := by
      intro k
      refine ⟨fun i => φ (localizedInvPrimePow S p k hpS hp) i, ?_⟩
      calc
        φ (localizedOne S)
            = φ ((p ^ k : ℤ) • localizedInvPrimePow S p k hpS hp) := by
                rw [localizedOne_eq_zsmul_invPrimePow S p k hpS hp]
        _ = (p ^ k : ℤ) • φ (localizedInvPrimePow S p k hpS hp) := by
              exact φ.map_zsmul (localizedInvPrimePow S p k hpS hp) (p ^ k : ℤ)
    have hone : φ (localizedOne S) = 0 := by
      exact vector_eq_zero_of_dvd_all_powers hp.two_le hdiv
    have hzero : localizedOne S = 0 := hφinj (by simpa using hone)
    have hone_ne : localizedOne S ≠ (0 : SupportedLocalizedIntegerGroup S) := by
      intro h
      have : ((localizedOne S : SupportedLocalizedIntegerGroup S) : ℚ) = (0 : ℚ) := by
        simpa using congrArg (fun q : SupportedLocalizedIntegerGroup S => (q : ℚ)) h
      norm_num [localizedOne] at this
    exact hone_ne hzero

end Omega.Zeta
