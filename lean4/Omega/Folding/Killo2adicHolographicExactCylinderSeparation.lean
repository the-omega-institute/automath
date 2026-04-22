import Omega.Folding.Killo2adicHolographicPrefixClassification

namespace Omega.Folding

/-- The first differing digit occurs at the zero-based position `j`: the first `j` digits agree,
but the digit at `j` does not. -/
def killoFirstDifferenceAt (q : ℕ) (a b : KilloStream q) (j : ℕ) : Prop :=
  killoPrefix q j a = killoPrefix q j b ∧ a j ≠ b j

private theorem killoCode_append {B q : ℕ} :
    ∀ l₁ l₂ : List (Fin q),
      killoCode B (l₁ ++ l₂) = killoCode B l₁ + B ^ l₁.length * killoCode B l₂
  | [], l₂ => by simp [killoCode]
  | d :: l₁, l₂ => by
      simp [killoCode, killoCode_append l₁ l₂, Nat.pow_succ, Nat.mul_add, Nat.mul_comm,
        Nat.mul_assoc, add_assoc]

private theorem killoRho_eq_prefix_add_tail
    {B q m n : ℕ} (hmn : m ≤ n) (a : KilloStream q) :
    ∃ t : ℕ, killoRho B q n a = killoRho B q m a + B ^ m * t := by
  let u : Fin n → Fin q := killoPrefix q n a
  refine ⟨killoCode B ((List.ofFn u).drop m), ?_⟩
  unfold killoRho
  have hsplit :
      killoCode B (List.ofFn u) =
        killoCode B ((List.ofFn u).take m) + B ^ m * killoCode B ((List.ofFn u).drop m) := by
    rw [← List.take_append_drop m (List.ofFn u), killoCode_append]
    simp [List.length_take, Nat.min_eq_left hmn]
  have htake :
      (List.ofFn u).take m = List.ofFn (killoPrefix q m a) := by
    have htakeFn : Fin.take m hmn u = killoPrefix q m a := by
      funext i
      rfl
    rw [← Fin.ofFn_take_eq_take_ofFn hmn u, htakeFn]
  simpa [htake] using hsplit

private theorem killoRho_mod_prefix
    {B q m n : ℕ} (hmn : m ≤ n) (a : KilloStream q) :
    killoRho B q n a ≡ killoRho B q m a [MOD B ^ m] := by
  rcases killoRho_eq_prefix_add_tail (B := B) (q := q) hmn a with ⟨t, ht⟩
  have hle : killoRho B q m a ≤ killoRho B q n a := by omega
  have hmod : killoRho B q m a ≡ killoRho B q n a [MOD B ^ m] := by
    rw [Nat.modEq_iff_dvd' hle]
    refine ⟨t, ?_⟩
    omega
  exact hmod.symm

private theorem killoRho_lt_pow
    {B q : ℕ} (hB : 1 < B) (hqB : q ≤ B) :
    ∀ n : ℕ, ∀ a : KilloStream q, killoRho B q n a < B ^ n
  | 0, _ => by simp [killoRho, killoCode]
  | n + 1, a => by
      let tail : KilloStream q := fun i => a i.succ
      have htail : killoRho B q n tail < B ^ n := killoRho_lt_pow hB hqB n tail
      have hB0 : 0 < B := lt_trans Nat.zero_lt_one hB
      have hdigit : (a 0).1 < B := lt_of_lt_of_le (a 0).2 hqB
      have hdigit_le : (a 0).1 ≤ B - 1 := Nat.le_pred_of_lt hdigit
      have htail_pos : 0 < B ^ n := pow_pos hB0 _
      have htail_le : killoRho B q n tail ≤ B ^ n - 1 := Nat.le_pred_of_lt htail
      have htailCode :
          killoCode B (List.ofFn fun i : Fin n => a (i.1 + 1)) = killoRho B q n tail := by
        rfl
      rw [killoRho, List.ofFn_succ, killoCode]
      simp [killoPrefix]
      rw [htailCode]
      have hbound :
          (a 0).1 + B * killoRho B q n tail ≤ (B - 1) + B * (B ^ n - 1) := by
        exact Nat.add_le_add hdigit_le (Nat.mul_le_mul_left _ htail_le)
      have hstrict :
          (B - 1) + B * (B ^ n - 1) < B ^ (n + 1) := by
        have hpow_ge : 1 ≤ B ^ n := Nat.succ_le_of_lt htail_pos
        have hmul_le : B ≤ B * B ^ n := by
          calc
            B = B * 1 := by rw [Nat.mul_one]
            _ ≤ B * B ^ n := Nat.mul_le_mul_left _ hpow_ge
        have hBminus : B - 1 < B := Nat.sub_lt (lt_trans Nat.zero_lt_one hB) zero_lt_one
        calc
          (B - 1) + B * (B ^ n - 1) < B + B * (B ^ n - 1) := by
            exact Nat.add_lt_add_of_lt_of_le hBminus (le_rfl)
          _ = B + (B * B ^ n - B) := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          _ = B * B ^ n := by exact Nat.add_sub_of_le hmul_le
          _ = B ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
      exact lt_of_le_of_lt hbound hstrict

/-- Paper label: `thm:killo-2adic-holographic-exact-cylinder-separation`. In the finite prefix
model, the first differing digit at position `j` forces exact `B^j` separation of the length-`n`
codes, and congruence modulo `B^n` is equivalent to equality of the first `n` digits. -/
theorem paper_killo_2adic_holographic_exact_cylinder_separation
    {B q : ℕ} (hB : 1 < B) (hqB : q ≤ B) :
    (∀ ⦃a b : KilloStream q⦄ ⦃n j : ℕ⦄, j < n → killoFirstDifferenceAt q a b j →
      killoRho B q n a ≡ killoRho B q n b [MOD B ^ j] ∧
        ¬ killoRho B q n a ≡ killoRho B q n b [MOD B ^ (j + 1)]) ∧
    (∀ n : ℕ, ∀ a b : KilloStream q,
      killoRho B q n a ≡ killoRho B q n b [MOD B ^ n] ↔ killoPrefix q n a = killoPrefix q n b) := by
  have hB0 : 0 < B := lt_trans Nat.zero_lt_one hB
  have hPrefixClass :=
    (paper_killo_2adic_holographic_prefix_classification (B := B) (q := q) hB0 hqB).1
  refine ⟨?_, ?_⟩
  · intro a b n j hjn hdiff
    rcases hdiff with ⟨hprefix, hdiffDigit⟩
    have hEqj : killoRho B q j a = killoRho B q j b := (hPrefixClass j a b).2 hprefix
    have hmodjA : killoRho B q n a ≡ killoRho B q j a [MOD B ^ j] :=
      killoRho_mod_prefix (B := B) (q := q) (m := j) (n := n) (Nat.le_of_lt hjn) a
    have hmodjB : killoRho B q n b ≡ killoRho B q j b [MOD B ^ j] :=
      killoRho_mod_prefix (B := B) (q := q) (m := j) (n := n) (Nat.le_of_lt hjn) b
    have hmodj : killoRho B q n a ≡ killoRho B q n b [MOD B ^ j] := by
      have hmodjB' : killoRho B q n b ≡ killoRho B q j a [MOD B ^ j] := by
        simpa [hEqj] using hmodjB
      exact hmodjA.trans hmodjB'.symm
    have hprefixSuccNe : killoPrefix q (j + 1) a ≠ killoPrefix q (j + 1) b := by
      intro hEq
      exact hdiffDigit (by simpa [killoPrefix] using congrFun hEq ⟨j, Nat.lt_succ_self j⟩)
    have hneqSucc : killoRho B q (j + 1) a ≠ killoRho B q (j + 1) b := by
      intro hEq
      exact hprefixSuccNe ((hPrefixClass (j + 1) a b).1 hEq)
    refine ⟨hmodj, ?_⟩
    intro hmodSucc
    have htruncA :
        killoRho B q n a ≡ killoRho B q (j + 1) a [MOD B ^ (j + 1)] :=
      killoRho_mod_prefix (B := B) (q := q) (m := j + 1) (n := n) (Nat.succ_le_of_lt hjn) a
    have htruncB :
        killoRho B q n b ≡ killoRho B q (j + 1) b [MOD B ^ (j + 1)] :=
      killoRho_mod_prefix (B := B) (q := q) (m := j + 1) (n := n) (Nat.succ_le_of_lt hjn) b
    have htrunc :
        killoRho B q (j + 1) a ≡ killoRho B q (j + 1) b [MOD B ^ (j + 1)] :=
      htruncA.symm.trans (hmodSucc.trans htruncB)
    have hltA : killoRho B q (j + 1) a < B ^ (j + 1) := killoRho_lt_pow hB hqB _ a
    have hltB : killoRho B q (j + 1) b < B ^ (j + 1) := killoRho_lt_pow hB hqB _ b
    have hEqSucc : killoRho B q (j + 1) a = killoRho B q (j + 1) b := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt hltA, Nat.mod_eq_of_lt hltB] at htrunc
      exact htrunc
    exact hneqSucc hEqSucc
  · intro n a b
    constructor
    · intro hmod
      have hltA : killoRho B q n a < B ^ n := killoRho_lt_pow hB hqB _ a
      have hltB : killoRho B q n b < B ^ n := killoRho_lt_pow hB hqB _ b
      have hEq : killoRho B q n a = killoRho B q n b := by
        rw [Nat.ModEq, Nat.mod_eq_of_lt hltA, Nat.mod_eq_of_lt hltB] at hmod
        exact hmod
      exact (hPrefixClass n a b).1 hEq
    · intro hprefix
      have hEq : killoRho B q n a = killoRho B q n b := (hPrefixClass n a b).2 hprefix
      simp [Nat.ModEq, hEq]

end Omega.Folding
