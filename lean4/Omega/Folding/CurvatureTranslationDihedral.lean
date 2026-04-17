import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.FiberWeightCountComplement

namespace Omega

/-- Curvature translation on `X m`: the one-step cyclic successor.
    thm:fold-curvature-dihedral-action -/
noncomputable def curvatureTranslation (x : X m) : X m :=
  X.stableSucc x

/-- Inverse curvature translation on `X m`: the one-step predecessor. -/
noncomputable def curvatureTranslationInv (x : X m) : X m :=
  X.stablePred x

/-- Canonical orbit section of the translation action through `0`. -/
noncomputable def curvatureTranslationSection (r : Fin (Nat.fib (m + 2))) : X m :=
  (curvatureTranslation (m := m)^[r.1]) (X.stableZero (m := m))

private theorem Nat.mod_add_mod_right' (a b n : Nat) (_hn : 0 < n) :
    (a % n + b) % n = (a + b) % n := by
  conv_rhs => rw [← Nat.mod_add_div a n]
  rw [Nat.add_assoc, Nat.add_comm (n * (a / n)), ← Nat.add_assoc, Nat.add_mul_mod_self_left]

private theorem complementAction_translation_conjugation (m : Nat) (hm : 2 ≤ m) (x : X m) :
    complementAction (m := m) (curvatureTranslation x) =
      curvatureTranslationInv (complementAction (m := m) x) := by
  apply X.eq_of_stableValue_eq
  have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := by
    calc
      Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
      _ = 2 := by native_decide
  have hm1 : 1 ≤ m := by omega
  have hc_lt : Nat.fib (m + 1) - 2 < Nat.fib (m + 2) := by
    have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
    omega
  set F : Nat := Nat.fib (m + 2)
  set c : Nat := Nat.fib (m + 1) - 2
  set v : Nat := stableValue x
  have hFpos : 0 < F := by
    simpa [F] using fib_succ_pos (m + 1)
  have hv_lt : v < F := by
    simpa [F, v] using stableValue_lt_fib x
  have hFm1_lt : F - 1 < F := by omega
  rw [curvatureTranslation, curvatureTranslationInv]
  rw [complementAction, X.stableValue_stableSub,
    X.stableValue_ofNat_lt c (by simpa [c, F] using hc_lt), X.stableValue_stableSucc x hm1]
  rw [X.stableValue_stablePred (complementAction (m := m) x) hm1, complementAction,
    X.stableValue_stableSub, X.stableValue_ofNat_lt c (by simpa [c, F] using hc_lt)]
  change (c + (F - ((v + 1) % F))) % F = (((c + (F - v)) % F + F - 1) % F)
  have hrhs :
      (((c + (F - v)) % F + F - 1) % F) = (c + (F - v) + (F - 1)) % F := by
    have hsplit :
        (((c + (F - v)) % F + F - 1) % F) = (((c + (F - v)) % F + (F - 1)) % F) := by
      congr 1
      omega
    rw [hsplit, Nat.mod_add_mod_right' _ _ _ hFpos]
  rw [hrhs]
  by_cases hwrap : v + 1 < F
  · rw [Nat.mod_eq_of_lt hwrap]
    have hshift : c + (F - v) + (F - 1) = c + (F - (v + 1)) + F := by omega
    rw [hshift, Nat.add_mod_right]
  · have htop : v + 1 = F := by omega
    rw [htop, Nat.mod_self, Nat.sub_zero]
    have hcollapse : c + (F - v) + (F - 1) = c + F := by omega
    rw [hcollapse]

/-- Paper-facing dihedral package for the curvature translation action. The complement action is
an involution, it conjugates translation to its inverse, and the translation orbit through `0`
is faithful on residues modulo `F_{m+2}`.
    thm:fold-curvature-dihedral-action -/
theorem paper_fold_curvature_dihedral_action (m : Nat) (hm : 2 ≤ m) :
    Function.Involutive (complementAction (m := m)) ∧
      (∀ x : X m,
        complementAction (m := m) (curvatureTranslation x) =
          curvatureTranslationInv (complementAction (m := m) x)) ∧
      Function.Injective (curvatureTranslationSection (m := m)) := by
  refine ⟨complementAction_involutive m hm, complementAction_translation_conjugation m hm, ?_⟩
  intro r s hrs
  apply Fin.ext
  have hm1 : 1 ≤ m := by omega
  have hval := congrArg stableValue hrs
  have hr :
      stableValue (curvatureTranslationSection (m := m) r) = r.1 := by
    simpa [curvatureTranslationSection, curvatureTranslation, X.stableValue_stableZero,
      Nat.zero_add, Nat.mod_eq_of_lt r.2] using
      (X.stableValue_stableSucc_iterate (X.stableZero (m := m)) r.1 hm1)
  have hs :
      stableValue (curvatureTranslationSection (m := m) s) = s.1 := by
    simpa [curvatureTranslationSection, curvatureTranslation, X.stableValue_stableZero,
      Nat.zero_add, Nat.mod_eq_of_lt s.2] using
      (X.stableValue_stableSucc_iterate (X.stableZero (m := m)) s.1 hm1)
  exact hr.symm.trans (hval.trans hs)

end Omega
