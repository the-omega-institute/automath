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

end Omega
