import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Zeta.AuditedEvenFirstCapacityKinkFibonacciJump

namespace Omega.Zeta

noncomputable section

/-- The audited-even minimal sector contributes at most `2^B` recoverable states per minimal
fiber, while each complementary fiber contributes its full size. -/
def xiFoldbinAuditedWindowCapacityUpperBound (m B : ℕ) : ℚ :=
  (Nat.fib m : ℚ) * min (auditedEvenFirstKink m : ℚ) ((2 : ℚ) ^ B) +
    ((2 : ℚ) ^ m - (Nat.fib m : ℚ) * auditedEvenFirstKink m)

/-- Normalize the audited capacity upper bound by the full `2^m` state count. -/
def xiFoldbinAuditedWindowSuccessRateCap (m B : ℕ) : ℚ :=
  xiFoldbinAuditedWindowCapacityUpperBound m B / (2 : ℚ) ^ m

/-- Paper label: `thm:xi-foldbin-audited-window-oracle-hard-cap`.

The `F_m` minimal fibers are capped individually by `2^B`, the complementary fibers contribute
fully, and dividing by the total `2^m` states yields the advertised success-rate hard cap. -/
theorem paper_xi_foldbin_audited_window_oracle_hard_cap (m B : ℕ) :
    xiFoldbinAuditedWindowCapacityUpperBound m B =
      (2 : ℚ) ^ m - (Nat.fib m : ℚ) * ((auditedEvenFirstKink m - 2 ^ B : ℕ) : ℚ) ∧
    xiFoldbinAuditedWindowSuccessRateCap m B =
      1 - ((Nat.fib m : ℚ) / (2 : ℚ) ^ m) * ((auditedEvenFirstKink m - 2 ^ B : ℕ) : ℚ) := by
  have hcap :
      xiFoldbinAuditedWindowCapacityUpperBound m B =
        (2 : ℚ) ^ m - (Nat.fib m : ℚ) * ((auditedEvenFirstKink m - 2 ^ B : ℕ) : ℚ) := by
    by_cases h : auditedEvenFirstKink m ≤ 2 ^ B
    · have hmin : min (auditedEvenFirstKink m : ℚ) ((2 : ℚ) ^ B) = auditedEvenFirstKink m := by
        apply min_eq_left
        exact_mod_cast h
      have hsub : auditedEvenFirstKink m - 2 ^ B = 0 := Nat.sub_eq_zero_of_le h
      simp [xiFoldbinAuditedWindowCapacityUpperBound, hmin, hsub]
    · have hlt : 2 ^ B < auditedEvenFirstKink m := lt_of_not_ge h
      have hle : 2 ^ B ≤ auditedEvenFirstKink m := Nat.le_of_lt hlt
      have hmin : min (auditedEvenFirstKink m : ℚ) ((2 : ℚ) ^ B) = (2 : ℚ) ^ B := by
        apply min_eq_right
        exact_mod_cast hle
      have hcast :
          (((auditedEvenFirstKink m - 2 ^ B : ℕ) : ℚ)) =
            (auditedEvenFirstKink m : ℚ) - (2 : ℚ) ^ B := by
        calc
          (((auditedEvenFirstKink m - 2 ^ B : ℕ) : ℚ))
              = (auditedEvenFirstKink m : ℚ) - ((2 ^ B : ℕ) : ℚ) := by
                  exact Nat.cast_sub hle
          _ = (auditedEvenFirstKink m : ℚ) - (2 : ℚ) ^ B := by
                norm_num
      rw [hcast]
      simp [xiFoldbinAuditedWindowCapacityUpperBound, hmin]
      ring
  refine ⟨hcap, ?_⟩
  rw [xiFoldbinAuditedWindowSuccessRateCap, hcap]
  have hpow_ne : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  field_simp [hpow_ne]

end

end Omega.Zeta
