import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.POM

private theorem fib_shifted_fusion_nat (a b : Nat) :
    Nat.fib (a + 2) * Nat.fib (b + 2) =
      Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b := by
  have hadd := Nat.fib_add (a + 1) b
  rw [show a + 1 + b + 1 = a + b + 2 by omega, show a + 1 + 1 = a + 2 by omega] at hadd
  have hb := Nat.fib_add_two (n := b)
  have ha := Nat.fib_add_two (n := a)
  rw [hb, Nat.mul_add, hadd, ha]
  ring

/-- Finite-basis rigidity for the rank-one fusion defect system after shifting indices by `2`.
    thm:pom-rankone-fusion-defect-finite-basis -/
theorem paper_pom_rankone_fusion_defect_finite_basis
    (G : Nat -> Real) (hseed0 : G 0 = 0) (hseed1 : G 1 = 1) (hseed2 : G 2 = 1)
    (hA1 : forall a : Nat, G (a + 2) * G 3 = G (a + 3) + G a)
    (hA2 : forall a : Nat, G (a + 2) * G 4 = G (a + 4) + G a)
    (hA3 : G 5 ^ 2 = G 8 + G 3 ^ 2) (hpos1 : 0 < G 3) (hpos2 : 0 < G 4) :
    forall a b : Nat, G (a + 2) * G (b + 2) = G (a + b + 2) + G a * G b := by
  let _ := hA3
  let _ := hpos2
  have hG4_poly : G 4 = G 3 ^ 2 - 1 := by
    have h := hA1 1
    norm_num at h
    rw [hseed1] at h
    nlinarith
  have hG5_poly : G 5 = G 4 * G 3 - 1 := by
    have h := hA1 2
    norm_num at h
    rw [hseed2] at h
    nlinarith
  have hG6_from_A2 : G 6 = G 4 ^ 2 - 1 := by
    have h := hA2 2
    norm_num at h
    rw [hseed2] at h
    nlinarith
  have hG6_from_A1 : G 6 = G 5 * G 3 - G 3 := by
    have h := hA1 3
    norm_num at h
    nlinarith
  have hG5_explicit : G 5 = G 3 ^ 3 - G 3 - 1 := by
    nlinarith [hG4_poly, hG5_poly]
  have hG6_explicit_A2 : G 6 = G 3 ^ 4 - 2 * G 3 ^ 2 := by
    nlinarith [hG4_poly, hG6_from_A2]
  have hG6_explicit_A1 : G 6 = G 3 ^ 4 - G 3 ^ 2 - 2 * G 3 := by
    nlinarith [hG4_poly, hG5_poly, hG6_from_A1]
  have hG3_quad : G 3 ^ 2 = 2 * G 3 := by
    nlinarith [hG6_explicit_A2, hG6_explicit_A1]
  have hG3 : G 3 = 2 := by
    nlinarith
  have hG4 : G 4 = 3 := by
    nlinarith [hG4_poly, hG3]
  have hrec1 : ∀ n : Nat, G (n + 3) = 2 * G (n + 2) - G n := by
    intro n
    have h := hA1 n
    rw [hG3] at h
    nlinarith
  have hrec2 : ∀ n : Nat, G (n + 4) = G (n + 3) + G (n + 2) := by
    intro n
    have h := hA2 n
    rw [hG4] at h
    have h' := hrec1 n
    nlinarith
  have hGfib_shift : ∀ n : Nat, G (n + 2) = Nat.fib (n + 2) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        match n with
        | 0 =>
            simpa using hseed2
        | 1 =>
            rw [hG3]
            norm_num
        | k + 2 =>
            have ih1 : G (k + 3) = Nat.fib (k + 3) := by
              simpa [Nat.add_assoc] using ih (k + 1) (by omega)
            have ih2 : G (k + 2) = Nat.fib (k + 2) := by
              simpa using ih k (by omega)
            rw [show k + 2 + 2 = k + 4 by omega, hrec2 k, ih1, ih2]
            have hfib : (Nat.fib (k + 4) : Real) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
              exact_mod_cast (Nat.fib_add_two (n := k + 2))
            simpa [add_comm, add_left_comm, add_assoc] using hfib.symm
  have hGfib : ∀ n : Nat, G n = Nat.fib n := by
    intro n
    match n with
    | 0 => simpa using hseed0
    | 1 => simpa using hseed1
    | m + 2 =>
        simpa using hGfib_shift m
  intro a b
  have hFibNat := fib_shifted_fusion_nat a b
  calc
    G (a + 2) * G (b + 2) = (Nat.fib (a + 2) : Real) * Nat.fib (b + 2) := by
      rw [hGfib (a + 2), hGfib (b + 2)]
    _ = Nat.fib (a + b + 2) + (Nat.fib a : Real) * Nat.fib b := by
      exact_mod_cast hFibNat
    _ = G (a + b + 2) + G a * G b := by
      rw [← hGfib (a + b + 2), ← hGfib a, ← hGfib b]

end Omega.POM
