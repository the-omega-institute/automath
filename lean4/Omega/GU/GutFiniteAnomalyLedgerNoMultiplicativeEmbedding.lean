import Omega.GU.AnomalyLedgerNoMultiplicative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- Concrete `2`-torsion obstruction for multiplicative encoding into a finite anomaly ledger.
    thm:gut-finite-anomaly-ledger-no-multiplicative-embedding -/
theorem paper_gut_finite_anomaly_ledger_no_multiplicative_embedding :
    ¬ ∃ Φ : {n : ℕ // 0 < n} → Fin 21 → ZMod 2,
      Φ ⟨1, by omega⟩ = 0 ∧
        (∀ m n : {n : ℕ // 0 < n},
          Φ ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ = Φ m + Φ n) ∧
        Function.Injective Φ := by
  intro h
  rcases h with ⟨Φ, h1, hmul, hinj⟩
  let p1 : {n : ℕ // 0 < n} := ⟨1, by omega⟩
  let p2 : {n : ℕ // 0 < n} := ⟨2, by omega⟩
  let p4 : {n : ℕ // 0 < n} := ⟨4, by omega⟩
  have h4 : Φ p4 = 0 := by
    calc
      Φ p4 = Φ p2 + Φ p2 := by
        simpa [p4, p2] using hmul p2 p2
      _ = 0 := by
        ext i
        simp only [Pi.add_apply, Pi.zero_apply]
        have hcast : (((Φ p2 i).val : ℕ) : ZMod 2) = Φ p2 i := by
          simp
        rw [← hcast]
        have hlt : (Φ p2 i).val < 2 := ZMod.val_lt (Φ p2 i)
        interval_cases hval : (Φ p2 i).val <;> native_decide
  have hEq : Φ p4 = Φ p1 := by
    simpa [p1] using h4.trans h1.symm
  have hp4_eq_p1 : p4 = p1 := hinj hEq
  have : (4 : ℕ) = 1 := congrArg Subtype.val hp4_eq_p1
  norm_num at this

end Omega.GU
