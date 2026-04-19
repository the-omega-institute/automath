import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittPkSparsification

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Polynomial congruence modulo `n`, defined by equality after mapping coefficients to `ZMod n`.
This local notation is scoped to the current namespace and matches the paper statement. -/
def PolyZModEq (n : ℕ) (P Q : Polynomial ℤ) : Prop :=
  Polynomial.map (Int.castRingHom (ZMod n)) P = Polynomial.map (Int.castRingHom (ZMod n)) Q

local notation:50 P " ≡ " Q " [ZMOD " n "]" => PolyZModEq n P Q

lemma polyZModEq_refl (n : ℕ) (P : Polynomial ℤ) : P ≡ P [ZMOD n] :=
  rfl

lemma polyZModEq_trans {n : ℕ} {P Q R : Polynomial ℤ} (hPQ : P ≡ Q [ZMOD n])
    (hQR : Q ≡ R [ZMOD n]) : P ≡ R [ZMOD n] := by
  exact hPQ.trans hQR

lemma polyZModEq_of_dvd {m n : ℕ} (hdiv : m ∣ n) {P Q : Polynomial ℤ}
    (h : P ≡ Q [ZMOD n]) : P ≡ Q [ZMOD m] := by
  unfold PolyZModEq at h ⊢
  have hcast :
      (ZMod.castHom hdiv (ZMod m)).comp (Int.castRingHom (ZMod n)) = Int.castRingHom (ZMod m) := by
    ext z
    simp
  simpa [Polynomial.map_map, hcast] using
    congrArg (Polynomial.map (ZMod.castHom hdiv (ZMod m))) h

lemma polyZModEq_comp_right {n : ℕ} {P Q R : Polynomial ℤ} (h : P ≡ Q [ZMOD n]) :
    P.comp R ≡ Q.comp R [ZMOD n] := by
  unfold PolyZModEq at h ⊢
  simpa [Polynomial.map_comp] using
    congrArg (fun S : Polynomial (ZMod n) => S.comp (Polynomial.map (Int.castRingHom (ZMod n)) R))
      h

lemma X_pow_comp_X_pow (a b : ℕ) :
    ((Polynomial.X : Polynomial ℤ) ^ a).comp ((Polynomial.X : Polynomial ℤ) ^ b) =
      (Polynomial.X : Polynomial ℤ) ^ (a * b) := by
  calc
    ((Polynomial.X : Polynomial ℤ) ^ a).comp ((Polynomial.X : Polynomial ℤ) ^ b) =
        ((Polynomial.X : Polynomial ℤ) ^ b) ^ a := Polynomial.X_pow_comp
    _ = (Polynomial.X : Polynomial ℤ) ^ (b * a) := by rw [pow_mul]
    _ = (Polynomial.X : Polynomial ℤ) ^ (a * b) := by rw [Nat.mul_comm]

lemma witt_iterated_descent_aux (p ell n : ℕ) (_hp : Nat.Prime p) (hell : 1 ≤ ell)
    (a : ℕ → Polynomial ℤ)
    (hdwork :
      ∀ j, 1 ≤ j →
        a (p ^ j) ≡ (a (p ^ (j - 1))).comp (Polynomial.X ^ p) [ZMOD p ^ j]) :
    a (p ^ (ell + n)) ≡ (a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (n + 1))) [ZMOD p ^ ell] := by
  induction n with
  | zero =>
      simpa [pow_one] using hdwork ell hell
  | succ n ih =>
      have hstep_raw :
          a (p ^ (ell + n + 1)) ≡
            (a (p ^ (ell + n))).comp (Polynomial.X ^ p) [ZMOD p ^ (ell + n + 1)] := by
        simpa [Nat.add_assoc] using hdwork (ell + n + 1) (Nat.succ_le_succ (Nat.zero_le _))
      have hpowe_dvd : p ^ ell ∣ p ^ (ell + n + 1) := by
        exact pow_dvd_pow p (Nat.le_add_right ell (n + 1))
      have hstep :
          a (p ^ (ell + n + 1)) ≡
            (a (p ^ (ell + n))).comp (Polynomial.X ^ p) [ZMOD p ^ ell] :=
        polyZModEq_of_dvd hpowe_dvd hstep_raw
      have hcomp :
          (a (p ^ (ell + n))).comp (Polynomial.X ^ p) ≡
            ((a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (n + 1)))).comp (Polynomial.X ^ p)
              [ZMOD p ^ ell] :=
        polyZModEq_comp_right (R := Polynomial.X ^ p) ih
      have hcollapse :
          ((a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (n + 1)))).comp (Polynomial.X ^ p) =
            (a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (n + 2))) := by
        rw [Polynomial.comp_assoc, X_pow_comp_X_pow]
        simp [pow_succ', Nat.mul_comm]
      refine polyZModEq_trans hstep ?_
      refine hcomp.trans ?_
      simpa [hcollapse] using
        (rfl :
          Polynomial.map (Int.castRingHom (ZMod (p ^ ell)))
              ((a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (n + 2)))) =
            Polynomial.map (Int.castRingHom (ZMod (p ^ ell)))
              ((a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (n + 2)))))

/-- Iterated descent of the Frobenius pushforward congruence from level `p^k` to modulus `p^ell`.
    prop:witt-frobenius-iterated-descent -/
theorem paper_witt_frobenius_iterated_descent (p k ell : ℕ) (hp : Nat.Prime p) (hell : 1 ≤ ell)
    (hke : ell ≤ k) (a : ℕ → Polynomial ℤ)
    (hdwork :
      ∀ j, 1 ≤ j →
        a (p ^ j) ≡ (a (p ^ (j - 1))).comp (Polynomial.X ^ p) [ZMOD p ^ j]) :
    a (p ^ k) ≡ (a (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (k - ell + 1))) [ZMOD p ^ ell] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hke
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_sub_cancel_left ell n] using
    witt_iterated_descent_aux p ell n hp hell a hdwork

end Omega.SyncKernelWeighted
