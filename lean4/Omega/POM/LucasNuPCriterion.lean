import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.POM.LucasPrimeCongruence
import Omega.POM.PrimitivePrimeLucas

namespace Omega.POM

open Omega.Zeta.LucasBarrier

private lemma pow_dvd_iff_succ_le_one_of_padicValNat_zero {p n k : ℕ}
    (hp : Nat.Prime p) (hn : n ≠ 0) (hval : padicValNat p n = 0) :
    p ^ k ∣ n ↔ k + 1 ≤ 1 := by
  constructor
  · intro hdiv
    have hk : k ≤ n.factorization p := by
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp hdiv
    rw [Nat.factorization_def n hp, hval] at hk
    omega
  · intro hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp

private lemma padicValNat_eq_one_of_dvd_not_sq {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hdiv : p ∣ n) (hnot_sq : ¬ p ^ 2 ∣ n) : padicValNat p n = 1 := by
  have hge : 1 ≤ padicValNat p n :=
    one_le_padicValNat_of_dvd hn hdiv
  have hlt : padicValNat p n < 2 := by
    have hnot_ge_two : ¬ 2 ≤ padicValNat p n := by
      intro htwo
      apply hnot_sq
      exact dvd_trans (pow_dvd_pow p htwo) pow_padicValNat_dvd
    omega
  omega

/-- Paper label: `cor:pom-lucas-nu-p-criterion`. -/
theorem paper_pom_lucas_nu_p_criterion (p k : ℕ) (hp : p ∈ [3, 5, 7, 11, 13]) :
    padicValNat p (Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount p) =
        Omega.POM.LucasPrimeCongruence.wieferichFingerprint p - 1 ∧
      (p ^ k ∣ Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount p ↔
        k + 1 ≤ Omega.POM.LucasPrimeCongruence.wieferichFingerprint p) := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_⟩
    · have hleft :
          padicValNat 3 (Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount 3) = 0 := by
          norm_num [Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two]
      have hright : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 3 = 1 := by
        norm_num [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two]
      rw [hleft, hright]
    · have hfp : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 3 = 1 := by
        norm_num [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two]
      simpa [hfp, Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two] using
        (pow_dvd_iff_succ_le_one_of_padicValNat_zero (p := 3) (n := 4) (k := k)
          (by decide) (by decide) (by native_decide))
  · refine ⟨?_, ?_⟩
    · have hleft :
          padicValNat 5 (Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount 5) = 0 := by
          norm_num [Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two]
      have hright : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 5 = 1 := by
        haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 5) (n := 10)
            (by decide) (by norm_num) (by norm_num))
      rw [hleft, hright]
    · have hfp : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 5 = 1 := by
        haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 5) (n := 10)
            (by decide) (by norm_num) (by norm_num))
      simpa [hfp, Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two] using
        (pow_dvd_iff_succ_le_one_of_padicValNat_zero (p := 5) (n := 22) (k := k)
          (by decide) (by decide) (by native_decide))
  · refine ⟨?_, ?_⟩
    · have hleft :
          padicValNat 7 (Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount 7) = 0 := by
          norm_num [Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two]
      have hright : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 7 = 1 := by
        haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 7) (n := 28)
            (by decide) (by norm_num) (by norm_num))
      rw [hleft, hright]
    · have hfp : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 7 = 1 := by
        haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 7) (n := 28)
            (by decide) (by norm_num) (by norm_num))
      simpa [hfp, Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two] using
        (pow_dvd_iff_succ_le_one_of_padicValNat_zero (p := 7) (n := 116) (k := k)
          (by decide) (by decide) (by native_decide))
  · refine ⟨?_, ?_⟩
    · have hleft :
          padicValNat 11 (Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount 11) = 0 := by
          norm_num [Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two]
      have hright : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 11 = 1 := by
        haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 11) (n := 198)
            (by decide) (by norm_num) (by norm_num))
      rw [hleft, hright]
    · have hfp : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 11 = 1 := by
        haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 11) (n := 198)
            (by decide) (by norm_num) (by norm_num))
      simpa [hfp, Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two] using
        (pow_dvd_iff_succ_le_one_of_padicValNat_zero (p := 11) (n := 3582) (k := k)
          (by decide) (by decide) (by native_decide))
  · refine ⟨?_, ?_⟩
    · have hleft :
          padicValNat 13 (Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount 13) = 0 := by
          norm_num [Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two]
      have hright : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 13 = 1 := by
        haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 13) (n := 520)
            (by decide) (by norm_num) (by norm_num))
      rw [hleft, hright]
    · have hfp : Omega.POM.LucasPrimeCongruence.wieferichFingerprint 13 = 1 := by
        haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
        simpa [Omega.POM.LucasPrimeCongruence.wieferichFingerprint, lucas, Nat.fib_add_two] using
          (padicValNat_eq_one_of_dvd_not_sq (p := 13) (n := 520)
            (by decide) (by norm_num) (by norm_num))
      simpa [hfp, Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount, lucas, Nat.fib_add_two] using
        (pow_dvd_iff_succ_le_one_of_padicValNat_zero (p := 13) (n := 20840) (k := k)
          (by decide) (by decide) (by native_decide))

end Omega.POM
