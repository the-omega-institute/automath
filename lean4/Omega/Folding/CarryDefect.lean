import Omega.Folding.FiberArithmetic

namespace Omega

namespace X

noncomputable section

/-! ## Fibonacci auxiliary lemmas -/

/-- F(m) + Nat.fib(m) = F(m+1), i.e., Nat.fib(m+1) + Nat.fib(m) = Nat.fib(m+2).
    aux:fib-succ-add-fib-eq -/
theorem fib_succ_add_fib_eq (m : Nat) :
    Nat.fib (m + 1) + Nat.fib m = Nat.fib (m + 2) := by
  show Nat.fib (m + 1) + Nat.fib m = Nat.fib (m + 2)
  have := Nat.fib_add_two (n := m)
  omega

/-- Nat.fib(m+2) - Nat.fib(m+1) = Nat.fib(m), from the Fibonacci recurrence.
    aux:fib-sub-eq -/
theorem fib_sub_eq (m : Nat) :
    Nat.fib (m + 2) - Nat.fib (m + 1) = Nat.fib m := by
  have := Nat.fib_add_two (n := m)
  omega

/-- Nat.fib m < F(m+1) for all m.
    aux:fib-lt-fib-succ-succ -/
theorem fib_lt_fib_succ_succ (m : Nat) : Nat.fib m < Nat.fib (m + 2) := by
  show Nat.fib m < Nat.fib (m + 2)
  have := Nat.fib_add_two (n := m)
  have := (Nat.fib_pos (n := m + 1)).mpr (by omega)
  omega

/-! ## Carry defect: value-level theorem -/

/-- Helper: stableValue(restrict z) = stableValue z % F(m+1) for z : X (m+1). -/
private theorem stableValue_restrict_eq_mod (z : X (m + 1)) :
    stableValue (X.restrict z) = stableValue z % Nat.fib (m + 2) := by
  have h1 := stableValue_restrict_mod z
  have h2 := stableValue_lt_fib (X.restrict z)
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1.symm

/-- Core modular identity: ((a + b) % F) % G = (a + b + κ * fib m) % G
    where F = F(m+2), G = F(m+1),
    κ = if a + b ≥ F then 1 else 0. -/
private theorem mod_mod_carry_identity (a b : Nat)
    (haF : a < Nat.fib (m + 3)) (hbF : b < Nat.fib (m + 3)) :
    ((a + b) % Nat.fib (m + 3)) % Nat.fib (m + 2) =
      (a + b + (if a + b ≥ Nat.fib (m + 3) then 1 else 0) * Nat.fib m)
        % Nat.fib (m + 2) := by
  have hFG : Nat.fib (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 1) := fib_succ_succ' (m + 1)
  have hGfib : Nat.fib (m + 1) + Nat.fib m = Nat.fib (m + 2) := fib_succ_add_fib_eq m
  split
  case isTrue hge =>
    simp only [Nat.one_mul]
    have hsubLt : a + b - Nat.fib (m + 3) < Nat.fib (m + 3) := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsubLt]
    -- Goal: (a + b - F) % G = (a + b + fib m) % G
    -- Key: (a+b+fib m) = (a+b-F) + G + G (since F + fib m = 2G)
    have step : a + b + Nat.fib m =
        (a + b - Nat.fib (m + 3)) + Nat.fib (m + 2) + Nat.fib (m + 2) := by omega
    rw [step, Nat.add_mod_right, Nat.add_mod_right]
  case isFalse hlt =>
    simp only [Nat.zero_mul, Nat.add_zero]
    push_neg at hlt
    rw [Nat.mod_eq_of_lt hlt]

/-- The value-level carry defect theorem.
    Paper: thm:pom-stable-addition-carry-defect-unique-element -/
theorem stableValue_restrict_stableAdd_carry (x y : X (m + 1)) :
    stableValue (X.restrict (X.stableAdd x y)) =
      (stableValue (X.restrict x) + stableValue (X.restrict y) +
        carryIndicator x y * Nat.fib m) % Nat.fib (m + 2) := by
  rw [stableValue_restrict_eq_mod, stableValue_stableAdd,
    stableValue_restrict_eq_mod x, stableValue_restrict_eq_mod y]
  have core := mod_mod_carry_identity (stableValue x) (stableValue y)
    (stableValue_lt_fib x) (stableValue_lt_fib y)
  have hif : (if stableValue x + stableValue y ≥ Nat.fib (m + 3) then 1 else 0) =
      carryIndicator x y := by
    unfold carryIndicator; rfl
  rw [hif] at core
  rw [core]
  -- Goal: (sv_x + sv_y + κ*fib m) % G = (sv_x%G + sv_y%G + κ*fib m) % G
  -- Reduce both sides to ((sv_x%G + sv_y%G) % G + (κ*fib m) % G) % G
  set G := Nat.fib (m + 2)
  rw [Nat.add_mod (stableValue x + stableValue y) (carryIndicator x y * Nat.fib m) G,
      Nat.add_mod (stableValue x) (stableValue y) G,
      ← Nat.add_mod (stableValue x % G + stableValue y % G)
        (carryIndicator x y * Nat.fib m) G]

/-- The carry defect theorem at stable word level.
    Paper: thm:pom-stable-addition-carry-defect-unique-element -/
theorem restrict_stableAdd_carry_defect (x y : X (m + 1)) :
    X.restrict (X.stableAdd x y) =
      X.stableAdd (X.stableAdd (X.restrict x) (X.restrict y))
        (if carryIndicator x y = 0 then X.stableZero else carryElement m) := by
  apply eq_of_stableValue_eq
  have hVal := stableValue_restrict_stableAdd_carry x y
  rw [hVal, stableValue_stableAdd, stableValue_stableAdd]
  -- Evaluate the stableValue of the if-expression
  have hSV_if : stableValue (if carryIndicator x y = 0 then X.stableZero else carryElement m) =
      carryIndicator x y * Nat.fib m := by
    by_cases hκ : carryIndicator x y = 0
    · simp [hκ, stableValue_stableZero]
    · have hκ1 : carryIndicator x y = 1 := by
        have := carryIndicator_le_one x y; omega
      rw [if_neg hκ, stableValue_carryElement, hκ1, Nat.one_mul]
  rw [hSV_if]
  -- Goal: (sv_rx + sv_ry + κ*fib m) % G = ((sv_rx + sv_ry) % G + κ*fib m) % G
  -- Both sides equal ((sv_rx + sv_ry) % G + (κ*fib m) % G) % G
  conv_lhs => rw [Nat.add_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl _)]

/-- Corollary: carry anchor at m=6.
    stableValue(carryElement 6) = Nat.fib 6 = 8.
    Paper: cor:pom-carry-defect-m6-anchor-8-34 -/
theorem carryElement_m6_value : stableValue (carryElement 6) = 8 := by
  rw [stableValue_carryElement]; native_decide

/-- Concrete: carryElement 5 has value Nat.fib 5 = 5.
    cor:pom-carry-defect-m5-value -/
theorem carryElement_m5_value : stableValue (carryElement 5) = 5 := by
  rw [stableValue_carryElement]; native_decide

/-- Concrete: carryElement 7 has value Nat.fib 7 = 13.
    cor:pom-carry-defect-m7-value -/
theorem carryElement_m7_value : stableValue (carryElement 7) = 13 := by
  rw [stableValue_carryElement]; native_decide

/-- The carry element is nonzero for m ≥ 2.
    prop:pom-carry-element-nonzero -/
theorem carryElement_ne_zero (hm : 2 ≤ m) : carryElement m ≠ X.stableZero := by
  intro h
  have h1 := congr_arg stableValue h
  rw [stableValue_carryElement, stableValue_stableZero] at h1
  have : 0 < Nat.fib m := (Nat.fib_pos (n := m)).mpr (by omega)
  omega

end

end X

/-- Paper label: carry indicator (κ) definition.
    def:pom-kappa -/
theorem paper_kappa_def (x y : X (m + 1)) :
    carryIndicator x y =
    if stableValue x + stableValue y ≥ Nat.fib (m + 3) then 1 else 0 := rfl

namespace X

-- ══════════════════════════════════════════════════════════════
-- Phase R310: carryElement m=8,9 + Fibonacci pattern
-- ══════════════════════════════════════════════════════════════

/-- cor:pom-carry-defect-m6-anchor-8-34 -/
theorem carryElement_m8_value : stableValue (carryElement 8) = 21 := by
  rw [stableValue_carryElement]; native_decide

/-- cor:pom-carry-defect-m6-anchor-8-34 -/
theorem carryElement_m9_value : stableValue (carryElement 9) = 34 := by
  rw [stableValue_carryElement]; native_decide

/-- Paper package. cor:pom-carry-defect-m6-anchor-8-34 -/
theorem paper_carryElement_fibonacci_pattern :
    stableValue (carryElement 5) = Nat.fib 5 ∧
    stableValue (carryElement 6) = Nat.fib 6 ∧
    stableValue (carryElement 7) = Nat.fib 7 ∧
    stableValue (carryElement 8) = Nat.fib 8 ∧
    stableValue (carryElement 9) = Nat.fib 9 := by
  refine ⟨carryElement_m5_value, carryElement_m6_value, carryElement_m7_value,
    carryElement_m8_value, carryElement_m9_value⟩

end X

end Omega
