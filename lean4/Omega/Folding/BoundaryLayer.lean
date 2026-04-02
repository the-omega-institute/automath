import Omega.Folding.FiberSpectrum

/-! ### Boundary layer counting

A stable word x ∈ X_m is a boundary element if both its first and last bits
are true: x[0] = true ∧ x[m-1] = true. The boundary count b(m) tracks how
many stable words lie in this "boundary layer". -/

namespace Omega

/-- The boundary count: number of stable words with both endpoints true.
    For m ≤ 1 this is vacuously 0 or trivial. -/
def cBoundaryCount : (m : Nat) → Nat
  | 0 => 0
  | 1 => (@Finset.univ (X 1) (fintypeX 1)).filter
      (fun x => x.1 ⟨0, by omega⟩ = true) |>.card
  | m + 2 => (@Finset.univ (X (m + 2)) (fintypeX (m + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨m + 1, by omega⟩ = true) |>.card

/-- Boundary count base values via native_decide. -/
theorem cBoundaryCount_three : cBoundaryCount 3 = 1 := by native_decide
theorem cBoundaryCount_four : cBoundaryCount 4 = 1 := by native_decide
theorem cBoundaryCount_five : cBoundaryCount 5 = 2 := by native_decide
/-- cor:bdry-m6-square-instance -/
theorem cBoundaryCount_six : cBoundaryCount 6 = 3 := by native_decide
theorem cBoundaryCount_seven : cBoundaryCount 7 = 5 := by native_decide
theorem cBoundaryCount_eight : cBoundaryCount 8 = 8 := by native_decide

/-- The boundary count follows a Fibonacci pattern: b(m) = F(m-2) for m = 3..8.
    b(3)=1=F(1), b(4)=1=F(2), b(5)=2=F(3), b(6)=3=F(4), b(7)=5=F(5), b(8)=8=F(6).
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_eq_fib (m : Nat) (hm1 : 3 ≤ m) (hm : m ≤ 8) :
    cBoundaryCount m = Nat.fib (m - 2) := by
  interval_cases m <;> native_decide

/-- The boundary gap: |X_m| - b(m) for the verified range.
    gap(6) = 21 - 3 = 18, gap(7) = 34 - 5 = 29, gap(8) = 55 - 8 = 47. -/
theorem boundary_gap_six : Fintype.card (X 6) - cBoundaryCount 6 = 18 := by
  rw [X.card_eq_fib, cBoundaryCount_six]; native_decide
theorem boundary_gap_seven : Fintype.card (X 7) - cBoundaryCount 7 = 29 := by
  rw [X.card_eq_fib, cBoundaryCount_seven]; native_decide
theorem boundary_gap_eight : Fintype.card (X 8) - cBoundaryCount 8 = 47 := by
  rw [X.card_eq_fib, cBoundaryCount_eight]; native_decide

/-- Fibonacci arithmetic: F(9) - F(2) = 34 - 1 = 33. -/
theorem boundary_gap_33_value : Nat.fib 9 - Nat.fib 2 = 33 := by native_decide

/-- The count of stable words with first bit true. -/
def cFirstBitTrueCount : (m : Nat) → Nat
  | 0 => 0
  | m + 1 => (@Finset.univ (X (m + 1)) (fintypeX (m + 1))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true) |>.card

/-- First-bit-true count base values. -/
theorem cFirstBitTrueCount_three : cFirstBitTrueCount 3 = 2 := by native_decide
theorem cFirstBitTrueCount_four : cFirstBitTrueCount 4 = 3 := by native_decide
theorem cFirstBitTrueCount_five : cFirstBitTrueCount 5 = 5 := by native_decide
theorem cFirstBitTrueCount_six : cFirstBitTrueCount 6 = 8 := by native_decide
theorem cFirstBitTrueCount_seven : cFirstBitTrueCount 7 = 13 := by native_decide

/-- The first-bit-true count equals F(m): #{x ∈ X_m : x[0]=true} = F(m) for m=3..7. -/
theorem cFirstBitTrueCount_eq_fib (m : Nat) (hm1 : 3 ≤ m) (hm : m ≤ 7) :
    cFirstBitTrueCount m = Nat.fib m := by
  interval_cases m <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R151: First-bit-true general Fibonacci count
-- ══════════════════════════════════════════════════════════════

/-- Embedding X_n into first-bit-true words of X_{n+2}: v ↦ (true, false, v). -/
private def fbtWord (n : Nat) (v : X n) : Word (n + 2) := fun i =>
  if i.val = 0 then true
  else if i.val = 1 then false
  else if h : i.val - 2 < n then v.1 ⟨i.val - 2, h⟩
  else false

private theorem fbtWord_no11 (n : Nat) (v : X n) : No11 (fbtWord n v) := by
  intro k hk hk1
  have hkLt : k < n + 2 := lt_of_get_eq_true hk
  have hk1Lt : k + 1 < n + 2 := lt_of_get_eq_true hk1
  rw [get_of_lt _ hkLt] at hk; rw [get_of_lt _ hk1Lt] at hk1
  simp only [fbtWord] at hk hk1
  by_cases h0 : k = 0
  · subst h0; simp at hk1
  · by_cases h1 : k = 1
    · subst h1; simp [show ¬((1 : Nat) = 0) from by omega] at hk
    · simp only [h0, ↓reduceIte, h1] at hk
      simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show ¬(k + 1 = 1) from by omega] at hk1
      by_cases hk_int : k - 2 < n
      · simp only [hk_int, ↓dite_true] at hk
        by_cases hk1_int : k + 1 - 2 < n
        · simp only [hk1_int, ↓dite_true] at hk1
          exact v.2 (k - 2)
            (by rw [get_of_lt v.1 hk_int]; exact hk)
            (by rw [get_of_lt v.1 (by omega)]
                have : (⟨k - 2 + 1, by omega⟩ : Fin n) = ⟨k + 1 - 2, hk1_int⟩ :=
                  Fin.ext (by simp; omega)
                rw [this]; exact hk1)
        · simp only [hk1_int, ↓dite_false] at hk1; exact absurd hk1 Bool.false_ne_true
      · simp only [hk_int, ↓dite_false] at hk; exact absurd hk Bool.false_ne_true

private theorem fbtWord_first (n : Nat) (v : X n) :
    fbtWord n v ⟨0, by omega⟩ = true := by simp [fbtWord]

private theorem fbtWord_at_shift (n : Nat) (v : X n) (j : Fin n) :
    fbtWord n v ⟨j.val + 2, by omega⟩ = v.1 j := by
  unfold fbtWord
  simp only [show j.val + 2 ≠ 0 from by omega, ↓reduceIte,
    show j.val + 2 ≠ 1 from by omega, show j.val + 2 - 2 < n from j.isLt, ↓dite_true]
  have : j.val + 2 - 2 = j.val := by omega
  simp [this]

/-- First-bit-true count equals card of X(m-2) for m ≥ 2.
    cor:parry-golden-three-levels -/
private theorem cFirstBitTrueCount_eq_card_shift (n : Nat) :
    cFirstBitTrueCount (n + 2) = Fintype.card (X n) := by
  rw [X.card_eq_fib]
  show ((@Finset.univ (X (n + 2)) (fintypeX (n + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true)).card = Nat.fib (n + 2)
  have hfib : (@Finset.univ (X n) (fintypeX n)).card = Nat.fib (n + 2) := by
    rw [@Finset.card_univ _ (fintypeX n)]
    rw [show @Fintype.card _ (fintypeX n) = (@Finset.univ _ (fintypeX n)).card from
      (@Finset.card_univ _ (fintypeX n)).symm]
    rw [show @Finset.univ _ (fintypeX n) = @Finset.univ _ (X.instFintype n) from by
      ext x; simp [Finset.mem_univ]]
    rw [@Finset.card_univ _ (X.instFintype n)]; exact X.card_eq_fib n
  rw [← hfib]; symm
  apply @Finset.card_bij (X n) (X (n + 2))
    (@Finset.univ _ (fintypeX n))
    ((@Finset.univ _ (fintypeX (n + 2))).filter (fun x => x.1 ⟨0, by omega⟩ = true))
    (fun v _ => ⟨fbtWord n v, fbtWord_no11 n v⟩)
  · intro v _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fbtWord_first n v
  · intro v1 _ v2 _ heq
    have heqw : fbtWord n v1 = fbtWord n v2 := congrArg Subtype.val heq
    apply Subtype.ext; funext i
    have := congrFun heqw ⟨i.val + 2, by omega⟩
    simp only [fbtWord_at_shift] at this; exact this
  · intro ⟨w, hw⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    -- w[0] = true, so w[1] = false (No11). Interior: w[2..m-1] is No11
    have hinterior : No11 (fun i : Fin n => w ⟨i.val + 2, by omega⟩) := by
      intro k hk hk1
      have hkLt := lt_of_get_eq_true hk; have hk1Lt := lt_of_get_eq_true hk1
      rw [get_of_lt _ hkLt] at hk; rw [get_of_lt _ hk1Lt] at hk1
      exact hw (k + 2)
        (by rw [get_of_lt w (by omega)]; exact hk)
        (by rw [get_of_lt w (by omega)]; exact hk1)
    refine ⟨⟨fun i => w ⟨i.val + 2, by omega⟩, hinterior⟩,
      @Finset.mem_univ _ (fintypeX n) _, ?_⟩
    apply Subtype.ext; funext i
    simp only [fbtWord]
    split_ifs with h0' h1' h2'
    · have : i = ⟨0, by omega⟩ := Fin.ext (by omega); rw [this]; exact hmem.symm
    · have : i = ⟨1, by omega⟩ := Fin.ext (by omega); rw [this]
      -- w[1] = false since w[0] = true and No11
      symm; by_contra h1t
      have : w ⟨1, by omega⟩ = true := by cases hw1 : w ⟨1, by omega⟩ <;> simp_all
      exact hw 0 (by rw [get_of_lt w (by omega)]; exact hmem)
        (by rw [get_of_lt w (by omega)]; exact this)
    · congr 1; exact Fin.ext (by simp; omega)
    · -- i.val ≥ n+2, impossible for Fin (n+2)
      exact absurd (show i.val < n + 2 from i.isLt) (by omega)

/-- #{x ∈ X_m : x[0] = true} = F(m) for all m ≥ 2.
    cor:parry-golden-three-levels -/
theorem cFirstBitTrueCount_eq_fib_general (m : Nat) (hm : 2 ≤ m) :
    cFirstBitTrueCount m = Nat.fib m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 2 + n = n + 2 from by omega, cFirstBitTrueCount_eq_card_shift n, X.card_eq_fib]

-- ══════════════════════════════════════════════════════════════
-- Phase R127: Boundary shift-4 uplift
-- ══════════════════════════════════════════════════════════════

/-- Boundary shift-4 uplift: |X_{n+4}^bdry| = |X_n| for n = 2..4.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryUplift_card (n : Nat) (hn1 : 2 ≤ n) (hn2 : n ≤ 4) :
    cBoundaryCount (n + 4) = Fintype.card (X n) := by
  rw [X.card_eq_fib]
  interval_cases n <;> native_decide

/-- Paper: thm:boundary-shift4-uplift-isomorphism -/
theorem paper_boundaryUplift_card (n : Nat) (hn1 : 2 ≤ n) (hn2 : n ≤ 4) :
    cBoundaryCount (n + 4) = Fintype.card (X n) :=
  boundaryUplift_card n hn1 hn2

-- ══════════════════════════════════════════════════════════════
-- Phase 201: Involution obstruction
-- ══════════════════════════════════════════════════════════════

/-- An involution on a finite set with no fixed points implies even cardinality.
    prop:bdry-three-layer-obstructs-free-z2 -/
theorem involution_no_fixedpoint_even {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (hinv : σ * σ = 1)
    (hno_fix : ∀ x : α, σ x ≠ x) :
    Even (Fintype.card α) := by
  -- σ.support = univ (no fixed points)
  have hsupp : σ.support = Finset.univ := by
    ext x; simp [Equiv.Perm.mem_support, hno_fix x]
  -- σ^2 = 1 implies 2 | σ.support.card (mathlib: two_dvd_card_support)
  have hsq : σ ^ 2 = 1 := by rwa [sq, Equiv.Perm.mul_def]
  have h2dvd := Equiv.Perm.two_dvd_card_support hsq
  rw [hsupp, Finset.card_univ] at h2dvd
  exact even_iff_two_dvd.mpr h2dvd

/-- A set of odd cardinality admits no fixed-point-free involution.
    prop:bdry-three-layer-obstructs-free-z2 -/
theorem odd_card_no_free_involution {α : Type*} [Fintype α] [DecidableEq α]
    (hodd : ¬ Even (Fintype.card α))
    (σ : Equiv.Perm α) (hinv : σ * σ = 1) :
    ∃ x : α, σ x = x := by
  by_contra hc
  push_neg at hc
  exact hodd (involution_no_fixedpoint_even σ hinv hc)

-- ══════════════════════════════════════════════════════════════
-- Phase 202: Sym-invariant grading obstruction
-- ══════════════════════════════════════════════════════════════

/-- No nontrivial Sym-invariant Z₂-grading on Fin 3.
    prop:bdry-sheet-parity-extension-obstruction-m7 -/
theorem no_nontrivial_sym_invariant_grading_fin3
    (f : Fin 3 → Fin 2)
    (hinv : ∀ σ : Equiv.Perm (Fin 3), ∀ x, f (σ x) = f x) :
    ∀ x y : Fin 3, f x = f y := by
  -- swap(0,1) gives f(0) = f(1); swap(0,2) gives f(0) = f(2)
  have h01 : f 0 = f 1 := by
    have := hinv (Equiv.swap 0 1) 0
    simp [Equiv.swap_apply_left] at this; exact this.symm
  have h02 : f 0 = f 2 := by
    have := hinv (Equiv.swap 0 2) 0
    simp [Equiv.swap_apply_left] at this; exact this.symm
  intro x y; fin_cases x <;> fin_cases y <;> simp_all

-- ══════════════════════════════════════════════════════════════
-- Phase 203: Pigeonhole bit-width bounds
-- ══════════════════════════════════════════════════════════════

/-- Distinguishing 3 alternatives requires more than 1 bit: no injection Fin 3 → Fin 2.
    cor:bdry-sheet-parity-extension-min-register -/
theorem three_alternative_needs_two_bits :
    ¬ ∃ (f : Fin 3 → Fin 2), Function.Injective f := by
  intro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  simp at h

/-- 2 bits suffice for 3 alternatives: injection Fin 3 → Fin 4 exists.
    cor:bdry-sheet-parity-extension-min-register -/
theorem three_alternative_two_bits_suffice :
    ∃ (f : Fin 3 → Fin 4), Function.Injective f :=
  ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 225: Fibonacci square identity
-- ══════════════════════════════════════════════════════════════

/-- F(2n+1) = F(n)² + F(n+1)². prop:bdry-fib-square-identity -/
theorem bdry_square_identity (n : Nat) :
    Nat.fib (2 * n + 1) = Nat.fib n ^ 2 + Nat.fib (n + 1) ^ 2 :=
  (fib_sq_add_sq n).symm

-- ══════════════════════════════════════════════════════════════
-- Phase R24: Three-window boundary sum uniqueness
-- ══════════════════════════════════════════════════════════════

/-- The only even triple 2 ≤ m1 < m2 < m3 with F(m1-2)+F(m2-2)+F(m3-2)=12 is (4,6,8).
    thm:bdry-three-window-sum12-unique-even-triple -/
theorem bdry_three_window_sum12_unique (m1 m2 m3 : Nat)
    (hm1_even : Even m1) (hm2_even : Even m2) (hm3_even : Even m3)
    (h12 : m1 < m2) (h23 : m2 < m3) (hm1_pos : 2 ≤ m1)
    (hsum : Nat.fib (m1 - 2) + Nat.fib (m2 - 2) + Nat.fib (m3 - 2) = 12) :
    m1 = 4 ∧ m2 = 6 ∧ m3 = 8 := by
  -- m3 ≤ 8: if m3 ≥ 10 (even), F(m3-2) ≥ F(8) = 21 > 12
  have hm3_le : m3 ≤ 8 := by
    by_contra h; push_neg at h
    have : 10 ≤ m3 := by obtain ⟨k, rfl⟩ := hm3_even; omega
    have : Nat.fib 8 ≤ Nat.fib (m3 - 2) := Nat.fib_mono (by omega)
    have : Nat.fib 8 = 21 := by native_decide
    omega
  -- Even constraints: m1 ∈ {2,4,6,...}, m2 ∈ {2,4,6,...}, m3 ∈ {2,4,6,8}
  -- With 2 ≤ m1 < m2 < m3 ≤ 8 and all even:
  -- m3 ∈ {4,6,8}, m2 < m3 and even, m1 < m2 and even, 2 ≤ m1
  obtain ⟨k3, rfl⟩ := hm3_even
  obtain ⟨k2, rfl⟩ := hm2_even
  obtain ⟨k1, rfl⟩ := hm1_even
  -- k3*2 ≤ 8 means k3 ≤ 4; k1*2 ≥ 2 means k1 ≥ 1; k1 < k2 < k3
  have hk3 : k3 ≤ 4 := by omega
  have hk1 : 1 ≤ k1 := by omega
  have hk12 : k1 < k2 := by omega
  have hk23 : k2 < k3 := by omega
  interval_cases k3 <;> interval_cases k2 <;> interval_cases k1 <;> simp_all [Nat.fib]

-- ══════════════════════════════════════════════════════════════
-- Phase R26: Boundary count extension to m=9,10
-- ══════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- prop:bdry-fib-square-identity -/
theorem cBoundaryCount_nine : cBoundaryCount 9 = 13 := by native_decide

set_option maxHeartbeats 800000 in
/-- prop:bdry-fib-square-identity -/
theorem cBoundaryCount_ten : cBoundaryCount 10 = 21 := by native_decide

set_option maxHeartbeats 800000 in
/-- Boundary count = F(m-2) for m ∈ [3,10].
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_eq_fib_extended (m : Nat) (hm1 : 3 ≤ m) (hm : m ≤ 10) :
    cBoundaryCount m = Nat.fib (m - 2) := by
  interval_cases m <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R145: General boundary-Fibonacci theorem
-- ══════════════════════════════════════════════════════════════

/-- The boundary embedding: v ∈ X_n maps to (1,0,v,0,1) ∈ X_{n+4}. -/
private def bdryToWord (n : Nat) (v : X n) : Word (n + 4) := fun i =>
  if i.val = 0 then true
  else if i.val = 1 then false
  else if h : i.val - 2 < n then v.1 ⟨i.val - 2, h⟩
  else if i.val = n + 2 then false
  else true

private theorem bdryToWord_get (n : Nat) (v : X n) (k : Nat) (hk : k < n + 4) :
    get (bdryToWord n v) k = bdryToWord n v ⟨k, hk⟩ := get_of_lt _ hk

private theorem bdryToWord_no11 (n : Nat) (v : X n) : No11 (bdryToWord n v) := by
  intro k hk hk1
  have hkLt : k < n + 4 := lt_of_get_eq_true hk
  have hk1Lt : k + 1 < n + 4 := lt_of_get_eq_true hk1
  rw [bdryToWord_get _ _ _ hkLt] at hk
  rw [bdryToWord_get _ _ _ hk1Lt] at hk1
  -- Case on k position
  simp only [bdryToWord] at hk hk1
  by_cases h0 : k = 0
  · subst h0; simp at hk1
  · by_cases h1 : k = 1
    · subst h1; simp [show ¬((1 : Nat) = 0) from by omega] at hk
    · simp only [h0, ↓reduceIte, h1] at hk
      simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte,
        show ¬(k + 1 = 1) from by omega] at hk1
      -- k ≥ 2, check if interior
      by_cases hk_int : k - 2 < n
      · simp only [hk_int, ↓dite_true] at hk
        by_cases hk1_int : k + 1 - 2 < n
        · -- Both k and k+1 interior
          simp only [hk1_int, ↓dite_true] at hk1
          exact v.2 (k - 2)
            (by rw [get_of_lt v.1 hk_int]; exact hk)
            (by rw [get_of_lt v.1 (by omega)]
                have : (⟨k - 2 + 1, by omega⟩ : Fin n) = ⟨k + 1 - 2, hk1_int⟩ :=
                  Fin.ext (by simp; omega)
                rw [this]; exact hk1)
        · -- k+1 at penultimate (false)
          simp only [hk1_int, ↓dite_false] at hk1
          by_cases hlast : k + 1 = n + 2
          · have hkEq : k = n + 1 := by omega
            subst k
            simp at hk1
          · simp at hk1
            omega
      · -- k ≥ n+2
        simp only [hk_int, ↓dite_false] at hk
        by_cases hlast : k = n + 2
        · simp [hlast] at hk
        · simp [hlast] at hk
          omega

private theorem bdryToWord_first (n : Nat) (v : X n) :
    bdryToWord n v ⟨0, by omega⟩ = true := by simp [bdryToWord]

private theorem bdryToWord_last (n : Nat) (v : X n) :
    bdryToWord n v ⟨n + 3, by omega⟩ = true := by
  simp only [bdryToWord, show ¬((n + 3 : Nat) = 0) from by omega, ↓reduceIte,
    show ¬((n + 3 : Nat) = 1) from by omega, show ¬(n + 3 - 2 < n) from by omega,
    show ¬((n + 3 : Nat) = n + 2) from by omega, ↓dite_false]

private theorem bdryToWord_at_shift (n : Nat) (v : X n) (j : Fin n) :
    bdryToWord n v ⟨j.val + 2, by omega⟩ = v.1 j := by
  unfold bdryToWord
  simp only [show j.val + 2 ≠ 0 from by omega, ↓reduceIte,
    show j.val + 2 ≠ 1 from by omega, show j.val + 2 - 2 < n from j.isLt, ↓dite_true]
  -- Goal: v.1 ⟨j.val + 2 - 2, _⟩ = v.1 j
  have : j.val + 2 - 2 = j.val := by omega
  simp [this]

/-- Boundary count equals card of X(m-4) for m ≥ 5.
    thm:boundary-shift4-uplift-isomorphism-general -/
private theorem cBoundaryCount_eq_card_shift (n : Nat) :
    cBoundaryCount (n + 5) = Fintype.card (X (n + 1)) := by
  -- Strategy: rewrite both sides as Nat.fib via X.card_eq_fib, then use card_bij
  -- to show the boundary-filtered set has the same cardinality
  rw [X.card_eq_fib]
  -- Now: boundary filter count = Nat.fib (n + 3)
  -- Show this by constructing a bijection with X(n+1) which has card fib(n+3)
  show ((@Finset.univ (X ((n + 3) + 2)) (fintypeX ((n + 3) + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨(n + 3) + 1, by omega⟩ = true)).card =
      Nat.fib (n + 3)
  -- Use the bounded version for small n, and induction with bdryToWord for general n
  -- Actually, we can directly show this equals Finset.card of X(n+1) filtered as univ
  -- The key is: boundary words biject with X(n+1) via bdryToWord/extract
  -- Approach: show filter.card = Finset.univ.card for X(n+1) via card_bij
  -- then Finset.univ.card = Fintype.card = fib(n+3) by X.card_eq_fib
  -- Prove (filter ...).card = Nat.fib(n+3) via bijection with X(n+1)
  -- Both use fintypeX instance consistently
  -- Step 1: Show filtered.card = @Finset.univ(fintypeX(n+1)).card via card_bij
  -- Step 2: @Finset.univ.card = Nat.fib(n+3) by native_decide or X.card_eq_fib
  suffices h : ((@Finset.univ (X (n + 5)) (fintypeX (n + 5))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨n + 4, by omega⟩ = true)).card =
      (@Finset.univ (X (n + 1)) (fintypeX (n + 1))).card from by
    rw [h]
    -- @Finset.univ(fintypeX(n+1)).card = @Fintype.card(fintypeX(n+1)) = Nat.fib(n+3)
    rw [@Finset.card_univ _ (fintypeX (n + 1))]
    -- Now: @Fintype.card(fintypeX(n+1)) = Nat.fib(n+3)
    -- Use that fintypeX and X.instFintype are both Fintype (X (n+1))
    -- They must give the same card by Subsingleton of Fintype
    have h1 := @Finset.card_univ _ (fintypeX (n + 1))
    have h2 := @Finset.card_univ _ (X.instFintype (n + 1))
    have h3 := X.card_eq_fib (n + 1)
    -- h3 : @Fintype.card _ (X.instFintype (n+1)) = Nat.fib(n+1+2)
    -- All Fintype instances on the same type produce univ of the same card
    -- Finset.univ always contains all elements, so both have card = |X(n+1)|
    -- Use Fintype.card_eq_of_equiv or show univ_eq
    have h4 : @Finset.univ _ (fintypeX (n + 1)) = @Finset.univ _ (X.instFintype (n + 1)) := by
      ext x; simp [Finset.mem_univ]
    rw [show @Fintype.card _ (fintypeX (n + 1)) = (@Finset.univ _ (fintypeX (n + 1))).card
      from h1.symm, h4, h2, h3]
  symm
  apply @Finset.card_bij (X (n + 1)) (X (n + 5))
    (@Finset.univ _ (fintypeX (n + 1)))
    ((@Finset.univ _ (fintypeX (n + 5))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨n + 4, by omega⟩ = true))
    (fun v _ => ⟨bdryToWord (n + 1) v, bdryToWord_no11 (n + 1) v⟩)
  · intro v _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨bdryToWord_first (n + 1) v, bdryToWord_last (n + 1) v⟩
  · intro v1 _ v2 _ heq
    have heqw : bdryToWord (n + 1) v1 = bdryToWord (n + 1) v2 :=
      congrArg Subtype.val heq
    apply Subtype.ext; funext i
    have := congrFun heqw ⟨i.val + 2, by omega⟩
    simp only [bdryToWord_at_shift] at this
    exact this
  · intro ⟨w, hw⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨h0, hlast⟩ := hmem
    have hinterior : No11 (fun i : Fin (n + 1) => w ⟨i.val + 2, by omega⟩) := by
      intro k hk hk1
      have hkLt := lt_of_get_eq_true hk; have hk1Lt := lt_of_get_eq_true hk1
      rw [get_of_lt _ hkLt] at hk; rw [get_of_lt _ hk1Lt] at hk1
      exact hw (k + 2)
        (by rw [get_of_lt w (by omega)]; exact hk)
        (by rw [get_of_lt w (by omega)]; exact hk1)
    refine ⟨⟨fun i => w ⟨i.val + 2, by omega⟩, hinterior⟩,
      @Finset.mem_univ _ (fintypeX (n + 1)) _, ?_⟩
    apply Subtype.ext; funext i
    simp only [bdryToWord]
    split_ifs with h0' h1' h2' h3'
    · have : i = ⟨0, by omega⟩ := Fin.ext (by omega); rw [this]; exact h0.symm
    · have : i = ⟨1, by omega⟩ := Fin.ext (by omega); rw [this]
      symm; by_contra h1t
      have h1true : w ⟨1, by omega⟩ = true := by cases hw1 : w ⟨1, by omega⟩ <;> simp_all
      exact hw 0 (by rw [get_of_lt w (by omega)]; exact h0)
        (by rw [get_of_lt w (by omega)]; exact h1true)
    · congr 1; exact Fin.ext (by simp; omega)
    · have : i = ⟨n + 3, by omega⟩ := Fin.ext (by omega); rw [this]
      symm; by_contra hnt
      have htrue : w ⟨n + 3, by omega⟩ = true := by cases hw1 : w ⟨n + 3, by omega⟩ <;> simp_all
      exact hw (n + 3) (by rw [get_of_lt w (by omega)]; exact htrue)
        (by rw [get_of_lt w (by omega)]; exact hlast)
    · have hiLast : i.val = n + 4 := by have := i.isLt; omega
      have : i = ⟨n + 4, by omega⟩ := Fin.ext hiLast
      rw [this]; exact hlast.symm

/-- Boundary count equals Fibonacci: b(m) = F(m-2) for all m ≥ 3.
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_eq_fib_general (m : Nat) (hm : 3 ≤ m) :
    cBoundaryCount m = Nat.fib (m - 2) := by
  match m, hm with
  | 3, _ => exact cBoundaryCount_three
  | 4, _ => exact cBoundaryCount_four
  | n + 5, _ =>
    rw [cBoundaryCount_eq_card_shift n, X.card_eq_fib, show n + 5 - 2 = n + 1 + 2 from by omega]

/-- Boundary gap at m=9: |X_9| - b(9) = F(11) - F(7) = 89 - 13 = 76.
    prop:bdry-fib-square-identity -/
theorem boundary_gap_nine : Fintype.card (X 9) - cBoundaryCount 9 = 76 := by
  rw [X.card_eq_fib, cBoundaryCount_nine]; native_decide

/-- Boundary gap at m=10: |X_10| - b(10) = F(12) - F(8) = 144 - 21 = 123.
    prop:bdry-fib-square-identity -/
theorem boundary_gap_ten : Fintype.card (X 10) - cBoundaryCount 10 = 123 := by
  rw [X.card_eq_fib, cBoundaryCount_ten]; native_decide

set_option maxHeartbeats 1600000 in
/-- Boundary count at m=11: b(11) = 34 = F(9).
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_eleven : cBoundaryCount 11 = 34 := by native_decide

set_option maxHeartbeats 3200000 in
/-- Boundary count at m=12: b(12) = 55 = F(10).
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_twelve : cBoundaryCount 12 = 55 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R27: Uplift second difference residual
-- ══════════════════════════════════════════════════════════════

/-- Second difference residual law: F(n+2) - F(n+1) = F(n).
    thm:bdry-uplift-second-difference-residual-law -/
theorem bdry_uplift_second_difference_residual :
    Nat.fib 11 - Nat.fib 10 = Nat.fib 9 ∧
    Nat.fib 12 - Nat.fib 11 = Nat.fib 10 ∧
    Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R32: Boundary count square identity
-- ══════════════════════════════════════════════════════════════

/-- Boundary count square identity: b(2m-1) = b(m)² + b(m+1)² for 3 ≤ m ≤ 5.
    This is the Fibonacci identity F(2n-3) = F(n-2)² + F(n-1)² verified computationally.
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_square_identity (m : Nat) (hm : 3 ≤ m) (hm2 : m ≤ 5) :
    cBoundaryCount (2 * m - 1) = cBoundaryCount m ^ 2 + cBoundaryCount (m + 1) ^ 2 := by
  interval_cases m <;> native_decide

/-- General boundary square identity: F(2m-3) = F(m-2)² + F(m-1)² for m ≥ 3.
    Direct consequence of F(2n+1) = F(n)² + F(n+1)² with n = m-2.
    prop:bdry-fib-square-identity-general -/
theorem cBoundaryCount_square_identity_general (m : Nat) (hm : 3 ≤ m) :
    Nat.fib (2 * m - 3) = Nat.fib (m - 2) ^ 2 + Nat.fib (m - 1) ^ 2 := by
  have h : 2 * m - 3 = 2 * (m - 2) + 1 := by omega
  have h1 : m - 2 + 1 = m - 1 := by omega
  rw [h, h1.symm]
  exact bdry_square_identity (m - 2)

/-- Endpoint fiber sum identity: F_m + 2·F_{m-1} + F_{m-2} = F_{m+2}.
    thm:pom-endpoint-fiber-sum -/
theorem endpoint_fiber_sum (m : Nat) (hm : 2 ≤ m) :
    Nat.fib m + 2 * Nat.fib (m - 1) + Nat.fib (m - 2) = Nat.fib (m + 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [show 2 + k - 1 = k + 1 from by omega, show 2 + k - 2 = k from by omega]
  show Nat.fib (2 + k) + 2 * Nat.fib (k + 1) + Nat.fib k = Nat.fib (2 + k + 2)
  have e1 : Nat.fib (2 + k) = Nat.fib (k + 2) := by ring_nf
  have e2 : Nat.fib (2 + k + 2) = Nat.fib (k + 4) := by ring_nf
  rw [e1, e2]
  have h1 := Omega.fib_succ_succ' k
  have h2 := Omega.fib_succ_succ' (k + 1)
  have h3 := Omega.fib_succ_succ' (k + 2)
  rw [h3, h2, h1]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase R143: Cyclic sector cardinality at m=6
-- ══════════════════════════════════════════════════════════════

/-- Computable non-boundary count: stable words without both endpoints true. -/
def cNonBoundaryCount (m : Nat) : Nat :=
  match m with
  | 0 => 0
  | 1 => (@Finset.univ (X 1) (fintypeX 1)).filter
      (fun x => ¬ (x.1 ⟨0, by omega⟩ = true)) |>.card
  | m + 2 => (@Finset.univ (X (m + 2)) (fintypeX (m + 2))).filter
      (fun x => ¬ (x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨m + 1, by omega⟩ = true)) |>.card

/-- Cyclic sector at m=6 has 18 elements.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem cyclicSector_card_six : cNonBoundaryCount 6 = 18 := by native_decide

/-- Cyclic + boundary = total at m=6: 18 + 3 = 21.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem cyclic_boundary_partition_six :
    cNonBoundaryCount 6 + cBoundaryCount 6 = Nat.fib 8 := by
  rw [cyclicSector_card_six, cBoundaryCount_six]; native_decide

/-- Paper: subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_cyclicSector_card_six : cNonBoundaryCount 6 = 18 :=
  cyclicSector_card_six

-- ══════════════════════════════════════════════════════════════
-- Phase R148: Both-ends-false count + cross endpoint count
-- ══════════════════════════════════════════════════════════════

/-- Count of stable words with both endpoints false. -/
def cBothEndsFalseCount : (m : Nat) → Nat
  | 0 => 0
  | 1 => (@Finset.univ (X 1) (fintypeX 1)).filter
      (fun x => x.1 ⟨0, by omega⟩ = false) |>.card
  | m + 2 => (@Finset.univ (X (m + 2)) (fintypeX (m + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = false ∧ x.1 ⟨m + 1, by omega⟩ = false) |>.card

/-- Both-ends-false embedding: v ∈ X_n maps to (false, v, false) ∈ X_{n+2}. -/
private def befWord (n : Nat) (v : X n) : Word (n + 2) := fun i =>
  if i.val = 0 then false
  else if h : i.val - 1 < n then v.1 ⟨i.val - 1, h⟩
  else false

private theorem befWord_no11 (n : Nat) (v : X n) : No11 (befWord n v) := by
  intro k hk hk1
  have hkLt : k < n + 2 := lt_of_get_eq_true hk
  have hk1Lt : k + 1 < n + 2 := lt_of_get_eq_true hk1
  rw [get_of_lt _ hkLt] at hk; rw [get_of_lt _ hk1Lt] at hk1
  simp only [befWord] at hk hk1
  by_cases h0 : k = 0
  · subst h0; simp at hk
  · simp only [h0, ↓reduceIte] at hk
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte] at hk1
    by_cases hk_int : k - 1 < n
    · simp only [hk_int, ↓dite_true] at hk
      by_cases hk1_int : k + 1 - 1 < n
      · simp only [hk1_int, ↓dite_true] at hk1
        exact v.2 (k - 1)
          (by rw [get_of_lt v.1 hk_int]; exact hk)
          (by rw [get_of_lt v.1 (by omega)]
              have : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k + 1 - 1, hk1_int⟩ :=
                Fin.ext (by simp; omega)
              rw [this]; exact hk1)
      · simp only [hk1_int, ↓dite_false] at hk1; exact absurd hk1 Bool.false_ne_true
    · simp only [hk_int, ↓dite_false] at hk; exact absurd hk Bool.false_ne_true

private theorem befWord_at_shift (n : Nat) (v : X n) (j : Fin n) :
    befWord n v ⟨j.val + 1, by omega⟩ = v.1 j := by
  unfold befWord
  simp only [show j.val + 1 ≠ 0 from by omega, ↓reduceIte,
    show j.val + 1 - 1 < n from j.isLt, ↓dite_true]
  have : j.val + 1 - 1 = j.val := by omega
  simp [this]

/-- Both-ends-false count equals card of X(m-2) for m ≥ 2.
    cor:parry-golden-three-levels -/
private theorem cBothEndsFalseCount_eq_card_shift (n : Nat) :
    cBothEndsFalseCount (n + 2) = Fintype.card (X n) := by
  rw [X.card_eq_fib]
  show ((@Finset.univ (X (n + 2)) (fintypeX (n + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = false ∧ x.1 ⟨n + 1, by omega⟩ = false)).card =
      Nat.fib (n + 2)
  -- Bijection X_n ↔ both-ends-false in X_{n+2}
  have hfib : (@Finset.univ (X n) (fintypeX n)).card = Nat.fib (n + 2) := by
    rw [@Finset.card_univ _ (fintypeX n)]
    have h4 : @Finset.univ _ (fintypeX n) = @Finset.univ _ (X.instFintype n) := by
      ext x; simp [Finset.mem_univ]
    have h5 := @Finset.card_univ _ (X.instFintype n)
    rw [show @Fintype.card _ (fintypeX n) = (@Finset.univ _ (fintypeX n)).card
      from (@Finset.card_univ _ (fintypeX n)).symm, h4, h5]
    exact X.card_eq_fib n
  rw [← hfib]
  symm
  apply @Finset.card_bij (X n) (X (n + 2))
    (@Finset.univ _ (fintypeX n))
    ((@Finset.univ _ (fintypeX (n + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = false ∧ x.1 ⟨n + 1, by omega⟩ = false))
    (fun v _ => ⟨befWord n v, befWord_no11 n v⟩)
  · intro v _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, befWord]
    exact ⟨by simp, by simp []⟩
  · intro v1 _ v2 _ heq
    have heqw : befWord n v1 = befWord n v2 := congrArg Subtype.val heq
    apply Subtype.ext; funext i
    have := congrFun heqw ⟨i.val + 1, by omega⟩
    simp only [befWord_at_shift] at this
    exact this
  · intro ⟨w, hw⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨h0, hlast⟩ := hmem
    have hinterior : No11 (fun i : Fin n => w ⟨i.val + 1, by omega⟩) := by
      intro k hk hk1
      have hkLt := lt_of_get_eq_true hk; have hk1Lt := lt_of_get_eq_true hk1
      rw [get_of_lt _ hkLt] at hk; rw [get_of_lt _ hk1Lt] at hk1
      exact hw (k + 1)
        (by rw [get_of_lt w (by omega)]; exact hk)
        (by rw [get_of_lt w (by omega)]; exact hk1)
    refine ⟨⟨fun i => w ⟨i.val + 1, by omega⟩, hinterior⟩,
      @Finset.mem_univ _ (fintypeX n) _, ?_⟩
    apply Subtype.ext; funext i
    simp only [befWord]
    split_ifs with h0' h1'
    · have : i = ⟨0, by omega⟩ := Fin.ext (by omega); rw [this]; exact h0.symm
    · congr 1; exact Fin.ext (by simp; omega)
    · have hiLast : i.val = n + 1 := by have := i.isLt; omega
      have : i = ⟨n + 1, by omega⟩ := Fin.ext hiLast
      rw [this]; exact hlast.symm

/-- #{u ∈ X_m : u₁=0, u_m=0} = F_m for m ≥ 2.
    cor:parry-golden-three-levels -/
theorem cBothEndsFalseCount_eq_fib (m : Nat) (hm : 2 ≤ m) :
    cBothEndsFalseCount m = Nat.fib m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 2 + n = n + 2 from by omega, cBothEndsFalseCount_eq_card_shift n, X.card_eq_fib]

-- ══════════════════════════════════════════════════════════════
-- Phase R155: Boundary shift-4 uplift bijection
-- ══════════════════════════════════════════════════════════════

/-- Boundary words: first and last bit are true (requires m ≥ 2).
    thm:boundary-shift4-uplift-isomorphism -/
def isBoundaryWord {m : Nat} (hm : 2 ≤ m) (w : Word m) : Prop :=
  w ⟨0, by omega⟩ = true ∧ w ⟨m - 1, by omega⟩ = true

/-- Shift-4 uplift: prepend [true, false], append [false, true].
    thm:boundary-shift4-uplift-isomorphism -/
def boundaryUpliftMap {n : Nat} (v : X n) : Word (n + 4) :=
  fun i =>
    if h0 : i.val = 0 then true
    else if h1 : i.val = 1 then false
    else if h2 : i.val = n + 2 then false
    else if h3 : i.val = n + 3 then true
    else v.1 ⟨i.val - 2, by have := i.isLt; omega⟩

/-- Strip: remove first two and last two bits.
    thm:boundary-shift4-uplift-isomorphism -/
def boundaryStripMap {n : Nat} (w : Word (n + 4)) : Word n :=
  fun i => w ⟨i.val + 2, by omega⟩

/-- The uplift map preserves the No11 property.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryUpliftMap_no11 {n : Nat} (v : X n) : No11 (boundaryUpliftMap v) := by
  intro i hi hi1
  simp only [get] at hi hi1
  split at hi <;> [skip; simp_all]
  split at hi1 <;> [skip; simp_all]
  rename_i hlt hlt1
  simp only [boundaryUpliftMap] at hi hi1
  -- Case split: i ∈ {0,1,n+2,n+3} or middle
  by_cases h0 : i = 0
  · subst h0; simp at hi hi1
  by_cases h1 : i = 1
  · subst h1; simp at hi
  by_cases h2 : i = n + 2
  · subst h2; simp at hi
  by_cases h3 : i = n + 3
  · subst h3; omega
  -- i ∉ {0,1,n+2,n+3}, so i ∈ [2..n+1]
  -- Also i+1 ∉ {0,1}, and we need i+1 ∉ {n+2,n+3} or handle those
  -- i ∈ [2..n+1], so i ≥ 2 and i ≤ n+1
  have hi_ge : 2 ≤ i := by omega
  have hi_le : i ≤ n + 1 := by omega
  -- Simplify hi: the ite chain leaves v.1 ⟨i - 2, _⟩
  simp only [show ¬(i = 0) from h0, show ¬(i = 1) from h1,
    show ¬(i = n + 2) from h2, show ¬(i = n + 3) from h3] at hi
  -- For i+1: it's in [3..n+2]. Check if i+1 = n+2 (→ false) or in middle
  simp only [show ¬(i + 1 = 0) from by omega, show ¬(i + 1 = 1) from by omega,
    show ¬(i + 1 = n + 3) from by omega] at hi1
  by_cases h4 : i + 1 = n + 2
  · -- i+1 = n+2 → boundaryUpliftMap returns false → hi1 : false = true
    simp [h4] at hi1
  · simp only [h4] at hi1
    -- Both in middle: hi : v.1 ⟨i - 2, _⟩ = true, hi1 : v.1 ⟨i + 1 - 2, _⟩ = true
    have hlt_a : i - 2 < n := by omega
    have hlt_b : i - 2 + 1 < n := by omega
    have hget1 : get v.1 (i - 2) = true := by
      simp [get, hlt_a]; exact hi
    have hieq : i - 2 + 1 = i + 1 - 2 := by omega
    have hget2 : get v.1 (i - 2 + 1) = true := by
      unfold get; simp only [hlt_b, ↓reduceDIte]
      rw [show (⟨i - 2 + 1, hlt_b⟩ : Fin n) = ⟨i + 1 - 2, by omega⟩ from Fin.ext hieq]
      exact hi1
    exact v.2 (i - 2) hget1 hget2

/-- The uplift produces a boundary word.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryUpliftMap_isBoundary {n : Nat} (v : X n) :
    isBoundaryWord (by omega : 2 ≤ n + 4) (boundaryUpliftMap v) := by
  refine ⟨?_, ?_⟩
  · simp [boundaryUpliftMap]
  · simp [boundaryUpliftMap, show n + 4 - 1 = n + 3 from by omega]

/-- Strip after uplift is the identity.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryStrip_uplift {n : Nat} (v : X n) :
    boundaryStripMap (boundaryUpliftMap v) = v.1 := by
  funext ⟨j, hj⟩
  show boundaryUpliftMap v ⟨j + 2, by omega⟩ = v.1 ⟨j, hj⟩
  simp only [boundaryUpliftMap, show ¬(j + 2 = 0) from by omega,
    show ¬(j + 2 = 1) from by omega, show ¬(j + 2 = n + 2) from by omega,
    show ¬(j + 2 = n + 3) from by omega, dite_false]
  show v.1 ⟨j + 2 - 2, _⟩ = v.1 ⟨j, hj⟩
  congr 1

/-- Stripping a boundary word preserves the No11 property.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryStripMap_no11_of_boundary {n : Nat} (w : X (n + 4))
    (_hwbd : isBoundaryWord (by omega : 2 ≤ n + 4) w.1) :
    No11 (boundaryStripMap w.1) := by
  intro i hi hi1
  have hi_lt : i < n := lt_of_get_eq_true hi
  have hi1_lt : i + 1 < n := lt_of_get_eq_true hi1
  rw [get_of_lt _ hi_lt] at hi
  rw [get_of_lt _ hi1_lt] at hi1
  have hi' : get w.1 (i + 2) = true := by
    rw [get_of_lt _ (by omega)]
    simpa [boundaryStripMap] using hi
  have hi1' : get w.1 (i + 3) = true := by
    rw [get_of_lt _ (by omega)]
    simpa [boundaryStripMap] using hi1
  exact w.2 (i + 2) hi' hi1'

/-- Stripping and uplifting recovers a boundary word.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryUplift_strip_boundary {n : Nat} (w : X (n + 4))
    (hwbd : isBoundaryWord (by omega : 2 ≤ n + 4) w.1) :
    boundaryUpliftMap ⟨boundaryStripMap w.1, boundaryStripMap_no11_of_boundary w hwbd⟩ = w.1 := by
  have hw1zero : w.1 ⟨1, by omega⟩ = false := by
    by_contra h1
    have hfirst : get w.1 0 = true := by
      simpa [get] using hwbd.1
    have hnext : get w.1 1 = true := by
      simpa [get] using h1
    exact (w.2 0 hfirst hnext).elim
  have hwn2zero : w.1 ⟨n + 2, by omega⟩ = false := by
    by_contra h1
    have hprev : get w.1 (n + 2) = true := by
      simpa [get] using h1
    have hlast : get w.1 (n + 3) = true := by
      simpa [get, show n + 4 - 1 = n + 3 from by omega] using hwbd.2
    exact (w.2 (n + 2) hprev hlast).elim
  funext i
  rcases i with ⟨iv, hiv⟩
  by_cases h0 : iv = 0
  · subst h0
    change true = w.1 ⟨0, by omega⟩
    simpa using hwbd.1.symm
  by_cases h1 : iv = 1
  · subst h1
    change false = w.1 ⟨1, by omega⟩
    simpa using hw1zero.symm
  by_cases h2 : iv = n + 2
  · subst h2
    simp [boundaryUpliftMap, hwn2zero]
  by_cases h3 : iv = n + 3
  · subst h3
    have hlast : w.1 ⟨n + 3, by omega⟩ = true := by
      simpa [show n + 4 - 1 = n + 3 from by omega] using hwbd.2
    simp [boundaryUpliftMap, hlast]
  · have h0' : iv ≠ 0 := h0
    have h1' : iv ≠ 1 := h1
    have h2' : iv ≠ n + 2 := h2
    have h3' : iv ≠ n + 3 := h3
    have hiv_ge : 2 ≤ iv := by omega
    have hidx : (⟨iv - 2 + 2, by omega⟩ : Fin (n + 4)) = ⟨iv, hiv⟩ := by
      apply Fin.ext
      exact Nat.sub_add_cancel hiv_ge
    change w.1 ⟨iv - 2 + 2, by simpa [Nat.sub_add_cancel hiv_ge] using hiv⟩ = w.1 ⟨iv, hiv⟩
    simpa [boundaryStripMap] using congrArg w.1 hidx

/-- Boundary words in `X (n+4)` form the image of shift-4 uplift.
    thm:boundary-shift4-uplift-isomorphism -/
def BoundaryWordSubtype (n : Nat) :=
  {w : X (n + 4) // isBoundaryWord (by omega : 2 ≤ n + 4) w.1}

/-- The shift-4 uplift gives a bijection onto the boundary-word subtype.
    thm:boundary-shift4-uplift-isomorphism -/
theorem boundaryUplift_bijective (n : Nat) :
    Function.Bijective (fun v : X n =>
      (⟨⟨boundaryUpliftMap v, boundaryUpliftMap_no11 v⟩,
        boundaryUpliftMap_isBoundary v⟩ : BoundaryWordSubtype n)) := by
  let f : X n → BoundaryWordSubtype n := fun v =>
    ⟨⟨boundaryUpliftMap v, boundaryUpliftMap_no11 v⟩, boundaryUpliftMap_isBoundary v⟩
  let g : BoundaryWordSubtype n → X n := fun w =>
    ⟨boundaryStripMap w.1.1, boundaryStripMap_no11_of_boundary w.1 w.2⟩
  have hleft : Function.LeftInverse g f := by
    intro v
    apply Subtype.ext
    exact boundaryStrip_uplift v
  have hright : Function.RightInverse g f := by
    intro w
    apply Subtype.ext
    apply Subtype.ext
    exact boundaryUplift_strip_boundary w.1 w.2
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R159: Mixed endpoint count
-- ══════════════════════════════════════════════════════════════

/-- Count of words with first bit ≠ last bit.
    cor:parry-golden-three-levels -/
def cMixedEndCount (m : Nat) : Nat :=
  if h : m ≥ 2 then
    (@Finset.univ (X m) (fintypeX m)).filter
      (fun x => x.1 ⟨0, by omega⟩ ≠ x.1 ⟨m - 1, by omega⟩) |>.card
  else 0

/-- Mixed-endpoint base values. -/
@[simp] theorem cMixedEndCount_two : cMixedEndCount 2 = 2 := by native_decide
@[simp] theorem cMixedEndCount_three : cMixedEndCount 3 = 2 := by native_decide

/-- Mixed-endpoint count equals `2·F_{m-1}` for all `m ≥ 2`.
    cor:parry-golden-three-levels -/
theorem cMixedEndCount_eq_two_fib (m : Nat) (hm : 2 ≤ m) :
    cMixedEndCount m = 2 * Nat.fib (m - 1) := by
  classical
  match m, hm with
  | 2, _ => simp
  | n + 3, _ =>
      let s : Finset (X (n + 3)) := @Finset.univ (X (n + 3)) (fintypeX (n + 3))
      let eqs : Finset (X (n + 3)) :=
        s.filter (fun x => x.1 ⟨0, by omega⟩ = x.1 ⟨n + 2, by omega⟩)
      have hsplit_total :
          eqs.card +
              (s.filter (fun x : X (n + 3) =>
                ¬ x.1 ⟨0, by omega⟩ = x.1 ⟨n + 2, by omega⟩)).card =
            s.card := by
        simpa [s, eqs] using
          (Finset.card_filter_add_card_filter_not
            (s := s) (p := fun x : X (n + 3) => x.1 ⟨0, by omega⟩ = x.1 ⟨n + 2, by omega⟩))
      have hsplit_eq :
          (eqs.filter (fun x : X (n + 3) => x.1 ⟨0, by omega⟩ = true)).card +
              (eqs.filter (fun x : X (n + 3) => ¬ x.1 ⟨0, by omega⟩ = true)).card =
            eqs.card := by
        simpa [eqs] using
          (Finset.card_filter_add_card_filter_not
            (s := eqs) (p := fun x : X (n + 3) => x.1 ⟨0, by omega⟩ = true))
      have hboundarySet :
          eqs.filter (fun x : X (n + 3) => x.1 ⟨0, by omega⟩ = true) =
            (@Finset.univ (X (n + 3)) (fintypeX (n + 3))).filter
              (fun x => x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨n + 2, by omega⟩ = true) := by
        ext x
        simp only [eqs, s, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hEq, h0⟩
          exact ⟨h0, hEq.symm.trans h0⟩
        · rintro ⟨h0, hlast⟩
          exact ⟨by simpa [h0, hlast], h0⟩
      have hboundary :
          (eqs.filter (fun x : X (n + 3) => x.1 ⟨0, by omega⟩ = true)).card =
            cBoundaryCount (n + 3) := by
        simpa [cBoundaryCount] using congrArg Finset.card hboundarySet
      have hfalseSet :
          eqs.filter (fun x : X (n + 3) => ¬ x.1 ⟨0, by omega⟩ = true) =
            (@Finset.univ (X (n + 3)) (fintypeX (n + 3))).filter
              (fun x => x.1 ⟨0, by omega⟩ = false ∧ x.1 ⟨n + 2, by omega⟩ = false) := by
        ext x
        simp only [eqs, s, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hEq, h0⟩
          have h0' : x.1 ⟨0, by omega⟩ = false := by
            simpa using h0
          exact ⟨h0', hEq.symm.trans h0'⟩
        · rintro ⟨h0, hlast⟩
          exact ⟨by simpa [h0, hlast], by simpa using h0⟩
      have hfalse :
          (eqs.filter (fun x : X (n + 3) => ¬ x.1 ⟨0, by omega⟩ = true)).card =
            cBothEndsFalseCount (n + 3) := by
        simpa [cBothEndsFalseCount] using congrArg Finset.card hfalseSet
      have hmixed :
          (s.filter (fun x : X (n + 3) => ¬ x.1 ⟨0, by omega⟩ = x.1 ⟨n + 2, by omega⟩)).card =
            cMixedEndCount (n + 3) := by
        simp [cMixedEndCount, s, show 2 ≤ n + 3 by omega]
      have hs : s.card = Nat.fib (n + 5) := by
        have hsCard : s.card = @Fintype.card (X (n + 3)) (fintypeX (n + 3)) := by
          simp [s]
        rw [hsCard]
        have h4 : @Finset.univ _ (fintypeX (n + 3)) = @Finset.univ _ (X.instFintype (n + 3)) := by
          ext x
          simp [Finset.mem_univ]
        have h5 := @Finset.card_univ _ (X.instFintype (n + 3))
        rw [show @Fintype.card _ (fintypeX (n + 3)) = (@Finset.univ _ (fintypeX (n + 3))).card from
          (@Finset.card_univ _ (fintypeX (n + 3))).symm, h4, h5]
        exact X.card_eq_fib (n + 3)
      have heqcount : cBoundaryCount (n + 3) + cBothEndsFalseCount (n + 3) = eqs.card := by
        rw [← hboundary, ← hfalse]
        exact hsplit_eq
      have hsum :
          cBoundaryCount (n + 3) + cBothEndsFalseCount (n + 3) + cMixedEndCount (n + 3) =
            Nat.fib (n + 5) := by
        rw [← heqcount, hmixed, hs] at hsplit_total
        exact hsplit_total
      have hfalseFib : cBothEndsFalseCount (n + 3) = Nat.fib (n + 3) := by
        exact cBothEndsFalseCount_eq_fib (n + 3) (by omega)
      have hboundaryFib : cBoundaryCount (n + 3) = Nat.fib (n + 1) := by
        simpa using cBoundaryCount_eq_fib_general (n + 3) (by omega)
      have hendpoint := endpoint_fiber_sum (n + 3) (by omega)
      simp only [show n + 3 - 1 = n + 2 from by omega, show n + 3 - 2 = n + 1 from by omega,
        show n + 3 + 2 = n + 5 from by omega] at hendpoint
      rw [hfalseFib, hboundaryFib] at hsum
      have hmixedFib : cMixedEndCount (n + 3) = 2 * Nat.fib (n + 2) := by
        omega
      simpa [show n + 3 - 1 = n + 2 by omega] using hmixedFib

/-- Mixed-endpoint count = 2·F_{m-1} for m = 2..8 (computational verification).
    cor:parry-golden-three-levels -/
theorem cMixedEndCount_eq_two_fib_bounded (m : Nat) (hm1 : 2 ≤ m) (hm2 : m ≤ 8) :
    cMixedEndCount m = 2 * Nat.fib (m - 1) := by
  interval_cases m <;> native_decide

end Omega
