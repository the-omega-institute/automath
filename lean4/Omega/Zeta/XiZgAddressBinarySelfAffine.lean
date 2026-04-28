import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Binary streams with no adjacent `true` digits, the symbolic ZG admissibility condition. -/
def xi_zg_address_binary_self_affine_admissible (s : ℕ → Bool) : Prop :=
  ∀ n, s n = true → s (n + 1) = false

/-- The symbolic address limit set. -/
def xi_zg_address_binary_self_affine_limit_set : Set (ℕ → Bool) :=
  {s | xi_zg_address_binary_self_affine_admissible s}

/-- Prefix a zero digit to an admissible symbolic address. -/
def xi_zg_address_binary_self_affine_prefix_zero (s : ℕ → Bool) : ℕ → Bool :=
  fun n => if n = 0 then false else s (n - 1)

/-- Prefix the forced `10` branch to an admissible symbolic address. -/
def xi_zg_address_binary_self_affine_prefix_one_zero (s : ℕ → Bool) : ℕ → Bool :=
  fun n => if n = 0 then true else if n = 1 then false else s (n - 2)

/-- Tail after the first digit. -/
def xi_zg_address_binary_self_affine_tail_one (s : ℕ → Bool) : ℕ → Bool :=
  fun n => s (n + 1)

/-- Tail after the forced leading `10` block. -/
def xi_zg_address_binary_self_affine_tail_two (s : ℕ → Bool) : ℕ → Bool :=
  fun n => s (n + 2)

lemma xi_zg_address_binary_self_affine_prefix_zero_admissible {s : ℕ → Bool}
    (hs : xi_zg_address_binary_self_affine_admissible s) :
    xi_zg_address_binary_self_affine_admissible
      (xi_zg_address_binary_self_affine_prefix_zero s) := by
  intro n hn
  by_cases hn0 : n = 0
  · simp [xi_zg_address_binary_self_affine_prefix_zero, hn0] at hn
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hprev : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
    have hnext : n + 1 - 1 = n := by omega
    have htail : s (n - 1 + 1) = false :=
      hs (n - 1) (by simpa [xi_zg_address_binary_self_affine_prefix_zero, hn0] using hn)
    simpa [xi_zg_address_binary_self_affine_prefix_zero, hn0, hnext, hprev] using htail

lemma xi_zg_address_binary_self_affine_prefix_one_zero_admissible {s : ℕ → Bool}
    (hs : xi_zg_address_binary_self_affine_admissible s) :
    xi_zg_address_binary_self_affine_admissible
      (xi_zg_address_binary_self_affine_prefix_one_zero s) := by
  intro n hn
  by_cases hn0 : n = 0
  · simp [xi_zg_address_binary_self_affine_prefix_one_zero, hn0]
  · by_cases hn1 : n = 1
    · simp [xi_zg_address_binary_self_affine_prefix_one_zero, hn1] at hn
    · have htwo : 2 ≤ n := by omega
      have hnext0 : n + 1 ≠ 0 := by omega
      have hnext1 : n + 1 ≠ 1 := by omega
      have hsub_next : n + 1 - 2 = n - 1 := by omega
      have hsub_step : n - 2 + 1 = n - 1 := by omega
      have htail : s (n - 2 + 1) = false :=
        hs (n - 2) (by
          simpa [xi_zg_address_binary_self_affine_prefix_one_zero, hn0, hn1] using hn)
      simpa [xi_zg_address_binary_self_affine_prefix_one_zero, hnext0, hnext1, hsub_next,
        hsub_step] using (fun _ : n ≠ 0 => htail)

lemma xi_zg_address_binary_self_affine_tail_one_admissible {s : ℕ → Bool}
    (hs : xi_zg_address_binary_self_affine_admissible s) :
    xi_zg_address_binary_self_affine_admissible
      (xi_zg_address_binary_self_affine_tail_one s) := by
  intro n hn
  exact hs (n + 1) hn

lemma xi_zg_address_binary_self_affine_tail_two_admissible {s : ℕ → Bool}
    (hs : xi_zg_address_binary_self_affine_admissible s) :
    xi_zg_address_binary_self_affine_admissible
      (xi_zg_address_binary_self_affine_tail_two s) := by
  intro n hn
  simpa [Nat.add_assoc] using hs (n + 2) hn

/-- Concrete symbolic form of the strict binary self-affine ZG address decomposition. -/
def xi_zg_address_binary_self_affine_statement (L : Nat) : Prop :=
  let K := xi_zg_address_binary_self_affine_limit_set
  2 ≤ 2 ^ L ∧
    Set.MapsTo xi_zg_address_binary_self_affine_prefix_zero K K ∧
      Set.MapsTo xi_zg_address_binary_self_affine_prefix_one_zero K K ∧
        K =
          xi_zg_address_binary_self_affine_prefix_zero '' K ∪
            xi_zg_address_binary_self_affine_prefix_one_zero '' K ∧
          Disjoint
            (xi_zg_address_binary_self_affine_prefix_zero '' K)
            (xi_zg_address_binary_self_affine_prefix_one_zero '' K) ∧
          Function.Injective (fun s : {s // s ∈ K} => (s : ℕ → Bool))

/-- Paper label: `thm:xi-zg-address-binary-self-affine`. -/
theorem paper_xi_zg_address_binary_self_affine (L : Nat) (hL : 1 ≤ L) :
    xi_zg_address_binary_self_affine_statement L := by
  dsimp [xi_zg_address_binary_self_affine_statement,
    xi_zg_address_binary_self_affine_limit_set]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases L with
    | zero => omega
    | succ L =>
        rw [Nat.pow_succ]
        have hpos : 0 < 2 ^ L := Nat.pow_pos (by norm_num)
        nlinarith
  · intro s hs
    exact xi_zg_address_binary_self_affine_prefix_zero_admissible hs
  · intro s hs
    exact xi_zg_address_binary_self_affine_prefix_one_zero_admissible hs
  · ext s
    constructor
    · intro hs
      by_cases h0 : s 0 = true
      · refine Or.inr ⟨xi_zg_address_binary_self_affine_tail_two s, ?_, ?_⟩
        · exact xi_zg_address_binary_self_affine_tail_two_admissible hs
        · funext n
          by_cases hn0 : n = 0
          · simp [xi_zg_address_binary_self_affine_prefix_one_zero, hn0, h0]
          · by_cases hn1 : n = 1
            · have h10 : s 1 = false := by simpa using hs 0 h0
              simp [xi_zg_address_binary_self_affine_prefix_one_zero, hn1, h10]
            · have hsub : n - 2 + 2 = n := by omega
              simp [xi_zg_address_binary_self_affine_prefix_one_zero,
                xi_zg_address_binary_self_affine_tail_two, hn0, hn1, hsub]
      · refine Or.inl ⟨xi_zg_address_binary_self_affine_tail_one s, ?_, ?_⟩
        · exact xi_zg_address_binary_self_affine_tail_one_admissible hs
        · funext n
          by_cases hn0 : n = 0
          · have hfalse : s 0 = false := by
              cases h : s 0 <;> simp [h] at h0 ⊢
            simp [xi_zg_address_binary_self_affine_prefix_zero, hn0, hfalse]
          · have hsub : n - 1 + 1 = n := by omega
            simp [xi_zg_address_binary_self_affine_prefix_zero,
              xi_zg_address_binary_self_affine_tail_one, hn0, hsub]
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact xi_zg_address_binary_self_affine_prefix_zero_admissible ht
      · exact xi_zg_address_binary_self_affine_prefix_one_zero_admissible ht
  · rw [Set.disjoint_left]
    rintro s ⟨a, ha, rfl⟩ ⟨b, hb, hEq⟩
    have h0 := congrFun hEq 0
    simp [xi_zg_address_binary_self_affine_prefix_zero,
      xi_zg_address_binary_self_affine_prefix_one_zero] at h0
  · intro a b h
    exact Subtype.ext h

end Omega.Zeta
