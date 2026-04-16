import Mathlib.Tactic
import Omega.Folding.MetallicTwoStateSFT
import Omega.Folding.OstrowskiMetallicTwoRuleNormalization

namespace Omega.Folding

open Omega.Folding.OstrowskiDenominators

lemma metallicPerronRoot_sq_nat (A : Nat) :
    let lam : Real := metallicPerronRoot (A : Real)
    lam ^ 2 = (A : Real) * lam + 1 := by
  dsimp
  have hquad : metallicPerronRoot (A : Real) ^ 2 - (A : Real) * metallicPerronRoot (A : Real) - 1 = 0 :=
    metallicPerronRoot_quadratic (A : Real)
  linarith

lemma metallicPerronRoot_inv_nat (A : Nat) (hA : 1 ≤ A) :
    let lam : Real := metallicPerronRoot (A : Real)
    lam ^ (-1 : ℤ) = lam - A := by
  dsimp
  have hAReal : (1 : Real) ≤ A := by
    exact_mod_cast hA
  have hpos : 0 < metallicPerronRoot (A : Real) := metallicPerronRoot_pos hAReal
  have hsq : metallicPerronRoot (A : Real) ^ 2 = (A : Real) * metallicPerronRoot (A : Real) + 1 :=
    metallicPerronRoot_sq_nat A
  rw [zpow_neg_one]
  apply inv_eq_of_mul_eq_one_right
  calc
    metallicPerronRoot (A : Real) * (metallicPerronRoot (A : Real) - A)
        = metallicPerronRoot (A : Real) ^ 2 - (A : Real) * metallicPerronRoot (A : Real) := by
            ring
    _ = 1 := by linarith

/-- Paper-facing Binet closed form for metallic Ostrowski denominators.
    thm:metallic-binet-closed-form -/
theorem paper_metallic_binet_closed_form (A n : Nat) (hA : 1 <= A) :
    let lam : Real := metallicPerronRoot (A : Real)
    (metallicDenom A n : Real) =
      (lam ^ (n + 2) + (-1 : Real) ^ n * lam ^ (-(n : Int))) / (lam ^ 2 + 1) := by
  dsimp
  set lam : Real := metallicPerronRoot (A : Real)
  have hAReal : (1 : Real) ≤ A := by
    exact_mod_cast hA
  have hlam_pos : 0 < lam := by
    simpa [lam] using metallicPerronRoot_pos hAReal
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hsq : lam ^ 2 = (A : Real) * lam + 1 := by
    simpa [lam] using metallicPerronRoot_sq_nat A
  have hinv : lam ^ (-1 : ℤ) = lam - A := by
    simpa [lam] using metallicPerronRoot_inv_nat A hA
  have hdenom_ne : lam ^ 2 + 1 ≠ 0 := by positivity
  have hpow3 : lam ^ 3 = (A : Real) * lam ^ 2 + lam := by
    calc
      lam ^ 3 = lam * lam ^ 2 := by ring
      _ = lam * ((A : Real) * lam + 1) := by rw [hsq]
      _ = (A : Real) * lam ^ 2 + lam := by ring
  let closed : Nat → Prop := fun k =>
    (metallicDenom A k : Real) =
      (lam ^ (k + 2) + (-1 : Real) ^ k * lam ^ (-(k : Int))) / (lam ^ 2 + 1)
  have h0 : closed 0 := by
    dsimp [closed]
    rw [show metallicDenom A 0 = 1 by simp [metallicDenom, ostrowskiDenom_zero]]
    apply (eq_div_iff hdenom_ne).2
    simp
  have h1 : closed 1 := by
    dsimp [closed]
    rw [show (metallicDenom A 1 : Real) = A by
      norm_num [metallicDenom, ostrowskiDenom_one]]
    apply (eq_div_iff hdenom_ne).2
    rw [show lam ^ (-(1 : Int)) = lam ^ (-1 : ℤ) by norm_num, hinv, hpow3]
    ring
  have hstep : ∀ k, closed k ∧ closed (k + 1) → closed (k + 1) ∧ closed (k + 2) := by
    intro k hk
    rcases hk with ⟨hk0, hk1⟩
    refine ⟨hk1, ?_⟩
    dsimp [closed] at hk0 hk1 ⊢
    have hk1norm : (metallicDenom A (k + 1) : Real) =
        (lam ^ (k + 1 + 2) + (-1 : Real) ^ (k + 1) * lam ^ (-((k + 1 : Nat) : Int))) /
          (lam ^ 2 + 1) := by
      simpa [show (-(↑k + 1 : ℤ)) = -((k + 1 : Nat) : Int) by omega] using hk1
    have hkexp : lam ^ (k + 1 + 2) = lam ^ (k + 3) := by
      exact congrArg (fun t : Nat => lam ^ t) (by omega)
    have hrec : (metallicDenom A (k + 2) : Real) =
        (A : Real) * metallicDenom A (k + 1) + metallicDenom A k := by
      exact_mod_cast metallicDenom_recurrence A k
    have hposRec : lam ^ (k + 4) = (A : Real) * lam ^ (k + 3) + lam ^ (k + 2) := by
      have hmulpow : lam ^ (k + 2) * lam = lam ^ (k + 3) := by
        calc
          lam ^ (k + 2) * lam = lam ^ (k + 2) * lam ^ 1 := by simp
          _ = lam ^ (k + 3) := by
            rw [← pow_add]
      calc
        lam ^ (k + 4) = lam ^ (k + 2) * lam ^ 2 := by
          rw [show k + 4 = (k + 2) + 2 by omega, pow_add]
        _ = lam ^ (k + 2) * ((A : Real) * lam + 1) := by rw [hsq]
        _ = (A : Real) * (lam ^ (k + 2) * lam) + lam ^ (k + 2) := by ring
        _ = (A : Real) * lam ^ (k + 3) + lam ^ (k + 2) := by rw [hmulpow]
    have hnegRec :
        lam ^ (-((k + 2 : Nat) : Int)) =
          lam ^ (-(k : Int)) - (A : Real) * lam ^ (-((k + 1 : Nat) : Int)) := by
      calc
        lam ^ (-((k + 2 : Nat) : Int))
            = lam ^ (-((k + 1 : Nat) : Int)) * lam ^ (-1 : ℤ) := by
                rw [show (-((k + 2 : Nat) : Int)) = (-((k + 1 : Nat) : Int)) + (-1 : ℤ) by omega]
                rw [zpow_add₀ hlam_ne]
        _ = lam ^ (-((k + 1 : Nat) : Int)) * (lam - A) := by rw [hinv]
        _ = lam ^ (-((k + 1 : Nat) : Int)) * lam - (A : Real) * lam ^ (-((k + 1 : Nat) : Int)) := by
              ring
        _ = lam ^ (-(k : Int)) - (A : Real) * lam ^ (-((k + 1 : Nat) : Int)) := by
              rw [show (-(k : Int)) = (-((k + 1 : Nat) : Int)) + 1 by omega, zpow_add₀ hlam_ne]
              rw [zpow_one]
    have hsign1 : (-1 : Real) ^ (k + 1) = -((-1 : Real) ^ k) := by
      rw [pow_succ]
      ring
    have hsign2 : (-1 : Real) ^ (k + 2) = (-1 : Real) ^ k := by
      rw [pow_succ, hsign1]
      ring
    calc
      (metallicDenom A (k + 2) : Real)
          = (A : Real) * metallicDenom A (k + 1) + metallicDenom A k := hrec
      _ = (A : Real) *
            ((lam ^ (k + 1 + 2) + (-1 : Real) ^ (k + 1) * lam ^ (-((k + 1 : Nat) : Int))) /
              (lam ^ 2 + 1)) +
            ((lam ^ (k + 2) + (-1 : Real) ^ k * lam ^ (-(k : Int))) / (lam ^ 2 + 1)) := by
              rw [hk1norm, hk0]
      _ = ((A : Real) *
            (lam ^ (k + 1 + 2) + (-1 : Real) ^ (k + 1) * lam ^ (-((k + 1 : Nat) : Int))) +
            (lam ^ (k + 2) + (-1 : Real) ^ k * lam ^ (-(k : Int)))) / (lam ^ 2 + 1) := by
              field_simp [hdenom_ne]
      _ = (lam ^ (k + 4) + (-1 : Real) ^ (k + 2) * lam ^ (-((k + 2 : Nat) : Int))) /
            (lam ^ 2 + 1) := by
              rw [hkexp, hsign1, hsign2, hposRec, hnegRec]
              ring
  have hpair : ∀ k, closed k ∧ closed (k + 1) := by
    intro k
    induction k with
    | zero =>
        exact ⟨h0, h1⟩
    | succ k ih =>
        exact hstep k ih
  exact (hpair n).1

end Omega.Folding
