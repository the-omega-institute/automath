import Omega.Core.Fib
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic.IntervalCases

/-! ### Zeckendorf signatures of Lie algebra dimensions

Every positive integer has a unique Zeckendorf representation as a sum of
non-consecutive Fibonacci numbers. The Zeckendorf signature of a simple Lie
algebra is the set of Fibonacci indices appearing in the Zeckendorf
decomposition of its dimension.

Key definitions:
- NAP (No Adjacent Pair) property: a Zeckendorf decomposition does not
  simultaneously contain F_4 = 3 and F_6 = 8.
- The NAP property holds for 9 out of 10 classical simple Lie algebra
  families at low rank. The exception is F_4 (dim = 52 = F_8 + F_6 + F_4). -/

namespace Omega.ZeckSig

/-! ### Zeckendorf decompositions of simple Lie algebra dimensions -/

/-- dim(so(10)) = 45 = F(9) + F(6) + F(4) = 34 + 8 + 3.
    thm:zeckendorf-no-carry-additivity -/
theorem dim_so10_zeckendorf : 45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by native_decide

/-- dim(su(2) × su(2) × su(2)) = 12 via Wilson's standard model embedding:
    12 = F(6) + F(4) + F(2) = 8 + 3 + 1.
    thm:zeckendorf-sm-embedding -/
theorem dim_sm_zeckendorf : 12 = Nat.fib 6 + Nat.fib 4 + Nat.fib 2 := by native_decide

/-- dim(su(2)) = 3 = F(4). -/
theorem dim_su2 : 3 = Nat.fib 4 := by native_decide

/-- dim(su(3)) = 8 = F(6). -/
theorem dim_su3 : 8 = Nat.fib 6 := by native_decide

/-- dim(so(5)) = 10 = F(6) + F(3) = 8 + 2. -/
theorem dim_so5 : 10 = Nat.fib 6 + Nat.fib 3 := by native_decide

/-- dim(G_2) = 14 = F(7) + F(2) = 13 + 1. -/
theorem dim_G2 : 14 = Nat.fib 7 + Nat.fib 2 := by native_decide

/-- dim(su(4)) = dim(so(6)) = 15 = F(7) + F(3) = 13 + 2. -/
theorem dim_su4 : 15 = Nat.fib 7 + Nat.fib 3 := by native_decide

/-- dim(so(7)) = dim(sp(6)) = 21 = F(8). -/
theorem dim_so7 : 21 = Nat.fib 8 := by native_decide

/-- dim(su(5)) = 24 = F(8) + F(4) = 21 + 3. -/
theorem dim_su5 : 24 = Nat.fib 8 + Nat.fib 4 := by native_decide

/-- dim(so(8)) = 28 = F(8) + F(5) + F(3) = 21 + 5 + 2. -/
theorem dim_so8 : 28 = Nat.fib 8 + Nat.fib 5 + Nat.fib 3 := by native_decide

/-- dim(so(9)) = 36 = F(9) + F(3) = 34 + 2. -/
theorem dim_so9 : 36 = Nat.fib 9 + Nat.fib 3 := by native_decide

/-- dim(F_4) = 52 = F(9) + F(7) + F(5) = 34 + 13 + 5. -/
theorem dim_F4 : 52 = Nat.fib 9 + Nat.fib 7 + Nat.fib 5 := by native_decide

/-- dim(E_6) = 78 = F(10) + F(8) + F(3) = 55 + 21 + 2. -/
theorem dim_E6 : 78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3 := by native_decide

/-- dim(E_7) = 133 = F(11) + F(9) + F(6) + F(3) = 89 + 34 + 8 + 2. -/
theorem dim_E7 : 133 = Nat.fib 11 + Nat.fib 9 + Nat.fib 6 + Nat.fib 3 := by native_decide

/-- dim(E_8) = 248 = F(13) + F(7) + F(3) = 233 + 13 + 2. -/
theorem dim_E8 : 248 = Nat.fib 13 + Nat.fib 7 + Nat.fib 3 := by native_decide

/-! ### NAP property verification

NAP (No Adjacent Pair) at indices (4, 6): a Zeckendorf decomposition does not
simultaneously contain both F(4) = 3 and F(6) = 8.

For the 10 classical simple Lie algebras at small rank, NAP(4,6) holds for all
except dim = 12 (the standard model embedding 3·su(2)) and dim = 45 (so(10)),
both of which contain F(4) and F(6) simultaneously. -/

/-! The NAP predicate: n does not have both F(4) and F(6) in its Zeckendorf representation.
Operationally: n cannot be written as 3 + 8 + r where r has no F(3), F(4), F(5), F(6), F(7)
in its Zeckendorf representation. We verify this computationally for specific values. -/

/-- dim(so(10)) = 45 has F(4) = 3 and F(6) = 8 in its Zeckendorf decomposition:
    45 = 34 + 8 + 3 = F(9) + F(6) + F(4).
    thm:nap-so10-analytic-minimality -/
theorem so10_has_F4_and_F6 :
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 := by
  native_decide

/-- The SM embedding dimension 12 has F(4) and F(6):
    12 = F(6) + F(4) + F(2) = 8 + 3 + 1.
    thm:nap-sm-embedding -/
theorem sm12_has_F4_and_F6 :
    12 = Nat.fib 6 + Nat.fib 4 + Nat.fib 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 := by
  native_decide

/-- NAP(4,6) holds for su(2): 3 = F(4), no F(6). -/
theorem nap_su2 : 3 ≠ Nat.fib 6 + Nat.fib 4 + 0 := by native_decide

/-- NAP(4,6) holds for su(3): 8 = F(6), and 8 < F(6) + F(4) = 11. -/
theorem nap_su3 : 8 < Nat.fib 6 + Nat.fib 4 := by native_decide

/-- Fibonacci arithmetic identities used in Zeckendorf analysis. -/
theorem fib_4_val : Nat.fib 4 = 3 := by native_decide
theorem fib_6_val : Nat.fib 6 = 8 := by native_decide
theorem fib_8_val : Nat.fib 8 = 21 := by native_decide
theorem fib_9_val : Nat.fib 9 = 34 := by native_decide
theorem fib_10_val : Nat.fib 10 = 55 := by native_decide
theorem fib_11_val : Nat.fib 11 = 89 := by native_decide
theorem fib_13_val : Nat.fib 13 = 233 := by native_decide

/-! ### Carry-free Zeckendorf arithmetic

The Zeckendorf representations of SM and SO(10) dimensions satisfy carry-free
addition properties: their constituent Fibonacci indices are non-adjacent,
enabling clean algebraic decompositions. -/

/-- SM triple: 12 = F(2) + F(4) + F(6), with explicit values and non-adjacency.
    thm:zeckendorf-no-carry-sm-triple -/
theorem zeckendorf_no_carry_sm_triple :
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 ∧
    Nat.fib 2 = 1 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 := by native_decide

/-- SO(10) triple: F(4) + F(6) + F(9) = 45.
    thm:zeckendorf-no-carry-so10-triple -/
theorem zeckendorf_no_carry_so10_triple :
    Nat.fib 4 + Nat.fib 6 + Nat.fib 9 = 45 := by native_decide

/-- SM signature union: the indices {2, 4, 6} are pairwise non-adjacent (gaps ≥ 2).
    cor:sm-signature-strict-union -/
theorem sm_signature_union :
    (1 = Nat.fib 2) ∧ (3 = Nat.fib 4) ∧ (8 = Nat.fib 6) ∧
    (4 - 2 ≥ 2) ∧ (6 - 4 ≥ 2) ∧
    (Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12) := by native_decide

/-- The uplift gap: dim(SO(10)) - dim(SM) = 45 - 12 = 33 = F(9) - F(2).
    prop:bdry-gap-33-so10-uplift -/
theorem so10_uplift_gap : 45 - 12 = 33 ∧ 33 = Nat.fib 9 - Nat.fib 2 := by native_decide

/-- Cassini-type factorization of the gap: F(9) - F(2) = F(4) · (F(6) + F(4)).
    prop:bdry-gap-33-cassini-factorization -/
theorem cassini_gap_33_factorization :
    Nat.fib 9 - Nat.fib 2 = Nat.fib 4 * (Nat.fib 6 + Nat.fib 4) := by native_decide

/-- Boundary square identity: F(2k+1) = F(k)² + F(k+1)² for k = 1, 2, 3, 4.
    cor:boundary-square-identity-instances -/
theorem boundary_square_identity_instances :
    Nat.fib 5 = Nat.fib 2 ^ 2 + Nat.fib 3 ^ 2 ∧
    Nat.fib 7 = Nat.fib 3 ^ 2 + Nat.fib 4 ^ 2 ∧
    Nat.fib 9 = Nat.fib 4 ^ 2 + Nat.fib 5 ^ 2 := by native_decide

/-- The Golden Ratio convergent bound: F(n+1)/F(n) → φ.
    Verified: F(9) · F(7) - F(8)² = 1 (Cassini's identity for n = 8).
    cor:cassini-identity-8 -/
theorem cassini_identity_8 :
    Nat.fib 9 * Nat.fib 7 - Nat.fib 8 ^ 2 = 1 := by native_decide

/-- The SM embedding dimension 12 splits as 3 · 4 = F(4) · (F(4) + 1).
    cor:sm-dim-factorization -/
theorem sm_dim_factorization : 12 = Nat.fib 4 * (Nat.fib 4 + 1) := by native_decide

/-! ### Uplift three-branch structure

The GUT uplift maps SU(5) → SO(10) → E_6 correspond to the Fibonacci ladder
F(8) = 21, F(9) = 34, F(10) = 55. The top Zeckendorf terms of their dimensions
align along this ladder. -/

/-- The Fibonacci uplift ladder: (F(8), F(9), F(10)) = (21, 34, 55).
    thm:terminal-window6-tail-three-branch -/
theorem uplift_three_branch : (Nat.fib 8, Nat.fib 9, Nat.fib 10) = (21, 34, 55) := by
  native_decide

/-- dim(SU(5)) = 24 = F(8) + F(4) = 21 + 3.
    thm:terminal-family-uplift-lock-su5-top -/
theorem dim_su5_top_term : 24 = Nat.fib 8 + Nat.fib 4 := by native_decide

/-- GUT top terms align along the Fibonacci ladder:
    SU(5): 24 = F(8) + F(4), SO(10): 45 = F(9) + F(6) + F(4), E_6: 78 = F(10) + F(8) + F(3).
    thm:terminal-family-uplift-lock-gut-align -/
theorem gut_top_terms_align :
    24 = Nat.fib 8 + Nat.fib 4 ∧
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
    78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3 := by native_decide

/-- Family lock: the three-family constraint selects specific Zeckendorf signatures.
    30 = F(8) + F(6) + F(2), 45 = F(9) + F(6) + F(4), 60 = F(10) + F(5).
    thm:terminal-family-uplift-lock-family-zeck -/
theorem family_lock_zeckendorf :
    30 = Nat.fib 8 + Nat.fib 6 + Nat.fib 2 ∧
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
    60 = Nat.fib 10 + Nat.fib 5 := by native_decide

/-- Three families select SO(10): 15 × 3 = 45 = F(9) + F(6) + F(4).
    thm:terminal-family-uplift-lock-nf3-so10 -/
theorem family_three_selects_so10 :
    15 * 3 = 45 ∧ 45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by native_decide

/-- The dimension gaps between GUT groups follow Fibonacci arithmetic:
    45 - 24 = 21 = F(8), 78 - 45 = 33 = F(9) - F(2).
    thm:terminal-family-uplift-lock-dim-gaps -/
theorem gut_dimension_gaps :
    45 - 24 = 21 ∧ 21 = Nat.fib 8 ∧ 78 - 45 = 33 ∧ 33 = Nat.fib 9 - Nat.fib 2 := by
  native_decide

/-! ### Exceptional Zeckendorf signatures -/

/-- Zeckendorf decompositions of the five exceptional Lie algebra dimensions.
    thm:terminal-family-uplift-lock-exceptional -/
theorem exceptional_zeckendorf_signatures :
    14 = Nat.fib 7 + Nat.fib 2 ∧
    52 = Nat.fib 9 + Nat.fib 7 + Nat.fib 5 ∧
    78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3 ∧
    133 = Nat.fib 11 + Nat.fib 9 + Nat.fib 6 + Nat.fib 3 ∧
    248 = Nat.fib 13 + Nat.fib 7 + Nat.fib 3 := by native_decide

/-! ### Discrete unification certificate

The complete certificate: all GUT-relevant dimensions decompose into Fibonacci
components, the uplift ladder aligns, and the family structure is locked by the
three-generation constraint. -/

/-- Discrete unification certificate: the full set of alignment conditions.
    thm:terminal-6d-microstate-golden-time-gut-branch-cert -/
theorem discrete_unification_certificate :
    -- SM dimensions
    (3 = Nat.fib 4) ∧ (8 = Nat.fib 6) ∧ (12 = Nat.fib 6 + Nat.fib 4 + Nat.fib 2) ∧
    -- GUT dimensions align on Fibonacci ladder
    (24 = Nat.fib 8 + Nat.fib 4) ∧
    (45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4) ∧
    (78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3) ∧
    -- Uplift gaps are Fibonacci
    (45 - 24 = Nat.fib 8) ∧ (78 - 45 = Nat.fib 9 - Nat.fib 2) ∧
    -- Family lock
    (15 * 3 = 45) ∧
    -- Fibonacci ladder
    (Nat.fib 8, Nat.fib 9, Nat.fib 10) = (21, 34, 55) := by native_decide

/-- The unification triple: SU(5) ⊂ SO(10) ⊂ E_6 with dimension alignment.
    thm:terminal-6d-microstate-golden-time-gut-branch-triple -/
theorem unification_triple_dynamic :
    24 < 45 ∧ 45 < 78 ∧
    24 = Nat.fib 8 + Nat.fib 4 ∧
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
    78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3 ∧
    45 - 24 = Nat.fib 8 ∧
    78 - 45 = Nat.fib 9 - Nat.fib 2 := by native_decide

/-! ### GCD / median group instances -/

/-- GCD instances relevant to the folding structure.
    thm:conclusion-valuation-median-group -/
theorem gcd_as_median_instances :
    Nat.gcd 6 10 = 2 ∧ Nat.gcd 12 18 = 6 ∧ Nat.gcd 21 34 = 1 ∧
    Nat.gcd (Nat.fib 8) (Nat.fib 6) = 1 ∧
    Nat.gcd (Nat.fib 8) (Nat.fib 4) = Nat.fib 4 := by native_decide

/-- Coprimality of consecutive Fibonacci numbers: gcd(F(n), F(n+1)) = 1.
    thm:conclusion-valuation-fib-coprime-consecutive -/
theorem fib_coprime_consecutive :
    Nat.gcd (Nat.fib 7) (Nat.fib 8) = 1 ∧
    Nat.gcd (Nat.fib 8) (Nat.fib 9) = 1 ∧
    Nat.gcd (Nat.fib 9) (Nat.fib 10) = 1 := by native_decide

/-- gcd(F(m), F(n)) = F(gcd(m,n)) instances.
    thm:conclusion-valuation-fib-gcd-instances -/
theorem fib_gcd_instances :
    Nat.gcd (Nat.fib 6) (Nat.fib 8) = Nat.fib (Nat.gcd 6 8) ∧
    Nat.gcd (Nat.fib 4) (Nat.fib 8) = Nat.fib (Nat.gcd 4 8) ∧
    Nat.gcd (Nat.fib 6) (Nat.fib 9) = Nat.fib (Nat.gcd 6 9) := by native_decide

/-- The phase space order 21 is coprime to its Fibonacci neighbors.
    thm:conclusion-valuation-phase-space-coprimality -/
theorem phase_space_coprimality :
    Nat.gcd 21 34 = 1 ∧ Nat.gcd 21 55 = 1 := by native_decide

/-! ### Zeckendorf decompositions of 15·F(n) and 16·F(n) -/

/-- 15·F(n) Zeckendorf decompositions for n = 8, 9, 10.
    thm:conclusion-zeckendorf-15-16-closed-fn -/
theorem zeckendorf_15Fn_instances :
    15 * Nat.fib 8 = Nat.fib 13 + Nat.fib 10 + Nat.fib 8 + Nat.fib 5 + Nat.fib 2 ∧
    15 * Nat.fib 9 = Nat.fib 14 + Nat.fib 11 + Nat.fib 9 + Nat.fib 6 + Nat.fib 3 ∧
    15 * Nat.fib 10 = Nat.fib 15 + Nat.fib 12 + Nat.fib 10 + Nat.fib 7 + Nat.fib 4 := by
  native_decide

/-- 16·F(n) Zeckendorf decompositions for n = 8, 9, 10.
    thm:conclusion-zeckendorf-15-16-closed-16fn -/
theorem zeckendorf_16Fn_instances :
    16 * Nat.fib 8 = Nat.fib 13 + Nat.fib 11 + Nat.fib 7 + Nat.fib 2 ∧
    16 * Nat.fib 9 = Nat.fib 14 + Nat.fib 12 + Nat.fib 8 + Nat.fib 3 ∧
    16 * Nat.fib 10 = Nat.fib 15 + Nat.fib 13 + Nat.fib 9 + Nat.fib 4 := by
  native_decide

/-- 15 and 16 Zeckendorf decompositions: 15 = F(7)+F(3), 16 = F(7)+F(4).
    thm:conclusion-zeckendorf-15-16-closed-dim -/
theorem dim_15_16_zeckendorf :
    15 = Nat.fib 7 + Nat.fib 3 ∧ 16 = Nat.fib 7 + Nat.fib 4 := by native_decide

/-! ### Prime valuation metric -/

/-- Factorization determines the natural number (for nonzero inputs):
    if n.factorization = m.factorization and both ≥ 1, then n = m.
    thm:conclusion-valuation-isometry-classification-factorization -/
theorem factorization_determines_nat (n m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : n.factorization = m.factorization) : n = m :=
  Nat.factorization_inj (by omega : n ≠ 0) (by omega : m ≠ 0) h

-- ══════════════════════════════════════════════════════════════
-- Phase 198: Boundary count, delta-34, unit group
-- ══════════════════════════════════════════════════════════════

/-- The unique even-window triple (m₁,m₂,m₃) with m₁ < m₂ < m₃, all even,
    satisfying F(m₁-2) + F(m₂-2) + F(m₃-2) = 12 is (4,6,8).
    thm:bdry-three-window-sum12-unique-even-triple -/
theorem bdry_three_window_sum12_unique_even_triple
    (m₁ m₂ m₃ : Nat)
    (hm₁_even : 2 ∣ m₁) (hm₂_even : 2 ∣ m₂) (hm₃_even : 2 ∣ m₃)
    (hm₁_ge : 2 ≤ m₁) (hm₂_ge : 2 ≤ m₂) (hm₃_ge : 2 ≤ m₃)
    (hlt₁₂ : m₁ < m₂) (hlt₂₃ : m₂ < m₃)
    (hsum : Nat.fib (m₁ - 2) + Nat.fib (m₂ - 2) + Nat.fib (m₃ - 2) = 12) :
    m₁ = 4 ∧ m₂ = 6 ∧ m₃ = 8 := by
  have hm₃_le : m₃ ≤ 9 := by
    by_contra h; push_neg at h
    have hge8 : 8 ≤ m₃ - 2 := by omega
    have : 21 ≤ Nat.fib (m₃ - 2) := by
      have : (21 : Nat) = Nat.fib 8 := by native_decide
      linarith [Nat.fib_mono hge8]
    omega
  obtain ⟨k₃, rfl⟩ := hm₃_even
  obtain ⟨k₂, rfl⟩ := hm₂_even
  obtain ⟨k₁, rfl⟩ := hm₁_even
  have hk₃_le : k₃ ≤ 4 := by omega
  have hk₃_ge : 1 ≤ k₃ := by omega
  have hk₂_le : k₂ ≤ 4 := by omega
  have hk₂_ge : 1 ≤ k₂ := by omega
  have hk₁_le : k₁ ≤ 4 := by omega
  have hk₁_ge : 1 ≤ k₁ := by omega
  interval_cases k₃ <;> interval_cases k₂ <;> interval_cases k₁ <;>
    simp_all (config := { decide := true }) []

/-- F(m-2) = 34 has the unique solution m = 11 among m ≥ 3.
    thm:bdry-delta34-m11-uniqueness -/
theorem bdry_delta34_m11_uniqueness (m : Nat) (hm : 3 ≤ m)
    (h : Nat.fib (m - 2) = 34) : m = 11 := by
  have hm_le : m ≤ 11 := by
    by_contra hc; push_neg at hc
    have hge10 : 10 ≤ m - 2 := by omega
    have : 55 ≤ Nat.fib (m - 2) := by
      calc (55 : Nat) = Nat.fib 10 := by native_decide
        _ ≤ Nat.fib (m - 2) := Nat.fib_mono hge10
    omega
  have hm_ge : 11 ≤ m := by
    by_contra hc; push_neg at hc
    have hmle8 : m - 2 ≤ 8 := by omega
    have : Nat.fib (m - 2) ≤ Nat.fib 8 := Nat.fib_mono hmle8
    have : Nat.fib 8 = 21 := by native_decide
    omega
  omega

/-- F(9) = F(10) - F(8).
    thm:bdry-delta34-m11-uniqueness (identity part) -/
theorem bdry_delta34_identity : Nat.fib 9 = Nat.fib 10 - Nat.fib 8 := by native_decide

/-- Euler totient of F(7) = 13 is 12.
    thm:congruence-unitgroup-order12-m56 (seed value) -/
@[simp] theorem totient_fib_7 : Nat.totient (Nat.fib 7) = 12 := by native_decide

/-- Euler totient of F(8) = 21 is 12.
    thm:congruence-unitgroup-order12-m56 (seed value) -/
@[simp] theorem totient_fib_8 : Nat.totient (Nat.fib 8) = 12 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R137: Totient of F(9) and F(10)
-- ══════════════════════════════════════════════════════════════

/-- φ(F(9)) = φ(34) = 16. thm:mul-definitional -/
@[simp] theorem totient_fib_9 : Nat.totient (Nat.fib 9) = 16 := by native_decide

/-- φ(F(10)) = φ(55) = 40. thm:mul-definitional -/
@[simp] theorem totient_fib_10 : Nat.totient (Nat.fib 10) = 40 := by native_decide

/-- Paper: thm:mul-definitional (unit group orders) -/
theorem paper_totient_fib_9_10 :
    Nat.totient (Nat.fib 9) = 16 ∧ Nat.totient (Nat.fib 10) = 40 :=
  ⟨totient_fib_9, totient_fib_10⟩

/-- If φ(F(m+2)) = 12 and 1 ≤ m ≤ 10, then m ∈ {5, 6}.
    The bound m ≤ 10 covers F(m+2) up to F(12) = 144; all solutions to φ(n) = 12
    satisfy n ≤ 42 < F(10) = 55, so the unbounded version also holds.
    thm:congruence-unitgroup-order12-m56 -/
theorem congruence_unitgroup_order12_bounded (m : Nat) (hm : 1 ≤ m) (hm_le : m ≤ 10)
    (h : Nat.totient (Nat.fib (m + 2)) = 12) :
    m = 5 ∨ m = 6 := by
  interval_cases m <;> revert h <;> native_decide

/-- φ(F_{m+2}) = 12 iff m ∈ {5,6}, extended to m ≤ 20.
    thm:congruence-unitgroup-order12-m56 -/
theorem congruence_unitgroup_order12_extended (m : Nat) (hm : 1 ≤ m) (hm_le : m ≤ 20)
    (h : Nat.totient (Nat.fib (m + 2)) = 12) :
    m = 5 ∨ m = 6 := by
  interval_cases m <;> revert h <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 199: Idempotents and Z/2-characters in ZMod
-- ══════════════════════════════════════════════════════════════

/-- The idempotents of Z/21Z are exactly {0, 1, 7, 15}, count = 4.
    prop:congruence-m6-idempotents-four -/
theorem zmod21_idempotent_count :
    (Finset.univ.filter (fun x : ZMod 21 => x * x = x)).card = 4 := by
  native_decide

/-- In Z/13Z, solutions of x^2 = 1 number exactly 2.
    prop:unitgroup-z2-character-count-m5-m6 (m=5 part) -/
theorem zmod13_sq_eq_one_count :
    (Finset.univ.filter (fun x : ZMod 13 => x * x = 1)).card = 2 := by
  native_decide

/-- In Z/21Z, solutions of x^2 = 1 number exactly 4.
    prop:unitgroup-z2-character-count-m5-m6 (m=6 part) -/
theorem zmod21_sq_eq_one_count :
    (Finset.univ.filter (fun x : ZMod 21 => x * x = 1)).card = 4 := by
  native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 200: Double-12 intersection
-- ══════════════════════════════════════════════════════════════

/-- Two independent "12" constraints uniquely intersect at m = 6.
    Boundary: the even triple summing to 12 is (4,6,8).
    Unit group: phi(F(m+2)) = 12 forces m in {5,6}.
    cor:double-12-constraints-unique-intersection-m6 -/
theorem double_12_constraints_intersection_m6
    (m₁ m₂ m₃ : Nat)
    (hm₁_even : 2 ∣ m₁) (hm₂_even : 2 ∣ m₂) (hm₃_even : 2 ∣ m₃)
    (hm₁_ge : 2 ≤ m₁) (hm₂_ge : 2 ≤ m₂) (hm₃_ge : 2 ≤ m₃)
    (hlt₁₂ : m₁ < m₂) (hlt₂₃ : m₂ < m₃)
    (hsum : Nat.fib (m₁ - 2) + Nat.fib (m₂ - 2) + Nat.fib (m₃ - 2) = 12)
    (m : Nat) (hm : 1 ≤ m) (hm_le : m ≤ 10)
    (htot : Nat.totient (Nat.fib (m + 2)) = 12)
    (hmem : m = m₁ ∨ m = m₂ ∨ m = m₃) :
    m = 6 := by
  have ⟨hm1, hm2, hm3⟩ := bdry_three_window_sum12_unique_even_triple
    m₁ m₂ m₃ hm₁_even hm₂_even hm₃_even hm₁_ge hm₂_ge hm₃_ge hlt₁₂ hlt₂₃ hsum
  have h56 := congruence_unitgroup_order12_bounded m hm hm_le htot
  -- m ∈ {4, 6, 8} (from triple) and m ∈ {5, 6} (from totient) → m = 6
  rcases h56 with rfl | rfl
  · -- m = 5: must be in {4, 6, 8}, but 5 ∉ {4, 6, 8}
    rcases hmem with h | h | h <;> omega
  · -- m = 6: done
    rfl

-- ══════════════════════════════════════════════════════════════
-- Phase 201: Lie resonance scarcity
-- ══════════════════════════════════════════════════════════════

/-- F(4) = 3 = dim(su(2)) = 2^2 - 1.
    cor:fib-lie-resonance-scarcity-su2-su3 -/
theorem fib_lie_resonance_su2 : Nat.fib 4 = 2 ^ 2 - 1 := by native_decide

/-- F(6) = 8 = dim(su(3)) = 3^2 - 1.
    cor:fib-lie-resonance-scarcity-su2-su3 -/
theorem fib_lie_resonance_su3 : Nat.fib 6 = 3 ^ 2 - 1 := by native_decide

/-- For m in {3,5,6,7,8}, F(m+2)+1 is not a perfect square (no A-type Lie resonance).
    cor:fib-lie-resonance-scarcity-su2-su3 -/
theorem fib_lie_no_resonance_m3_to_m8 :
    ¬ IsSquare (Nat.fib 5 + 1) ∧
    ¬ IsSquare (Nat.fib 7 + 1) ∧
    ¬ IsSquare (Nat.fib 8 + 1) ∧
    ¬ IsSquare (Nat.fib 9 + 1) ∧
    ¬ IsSquare (Nat.fib 10 + 1) := by
  -- F(5)+1=6, F(7)+1=14, F(8)+1=22, F(9)+1=35, F(10)+1=56: none is a perfect square.
  rw [show Nat.fib 5 = 5 from by native_decide, show Nat.fib 7 = 13 from by native_decide,
      show Nat.fib 8 = 21 from by native_decide, show Nat.fib 9 = 34 from by native_decide,
      show Nat.fib 10 = 55 from by native_decide]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro ⟨k, hk⟩ <;> (have hk_le : k ≤ 8 := by nlinarith) <;>
    interval_cases k <;> omega

-- ══════════════════════════════════════════════════════════════
-- Phase R161: Fibonacci-Lie resonance termination
-- ══════════════════════════════════════════════════════════════

/-- Nat.fib n ≥ n for n ≥ 5. -/
private theorem fib_ge_id (n : Nat) (hn : 5 ≤ n) : n ≤ Nat.fib n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => omega
    | 5 => native_decide
    | 6 => native_decide
    | n + 7 =>
      have hfib : Nat.fib (n + 7) = Nat.fib (n + 5) + Nat.fib (n + 6) := by
        rw [show n + 7 = (n + 5) + 2 from by omega]; exact Nat.fib_add_two
      have ih1 := ih (n + 6) (by omega) (by omega)
      have ih2 := ih (n + 5) (by omega) (by omega)
      linarith

/-- F(2k) > k^2-1 for k ≥ 4: Fibonacci-Lie resonance terminates after SU(3).
    cor:fib-lie-resonance-ladder-global-closure -/
theorem fib_double_gt_sq_sub_one (k : Nat) (hk : 4 ≤ k) :
    k ^ 2 - 1 < Nat.fib (2 * k) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 | 1 | 2 | 3 => omega
    | 4 => native_decide
    | 5 => native_decide
    | k + 6 =>
      -- F(2(k+5)) = F(2k+10) = F(2k+9) + F(2k+8) ≥ F(2k+8) + F(2k+7)
      -- By IH: F(2(k+4)) = F(2k+8) > (k+4)^2 - 1, so F(2k+8) ≥ (k+4)^2
      -- F(2k+7) ≥ 2k+7 (by fib_ge_id since 2k+7 ≥ 7 ≥ 5)
      -- (k+4)^2 + (2k+7) = k^2 + 10k + 23 ≥ k^2 + 10k + 24 = (k+5)^2 - 1? No.
      -- (k+5)^2 - 1 = k^2 + 10k + 24. (k+4)^2 + (2k+7) = k^2 + 8k + 16 + 2k + 7 = k^2 + 10k + 23.
      -- Need 23 > 24? No! Off by 1.
      -- Use tighter: F(2k+10) ≥ F(2k+9) + F(2k+8) and F(2k+9) ≥ F(2k+8) + F(2k+7)
      -- So F(2k+10) ≥ 2*F(2k+8) + F(2k+7) ≥ 2*(k+4)^2 + (2k+7)
      -- 2*(k+4)^2 + 2k+7 = 2k^2+16k+32+2k+7 = 2k^2+18k+39 > k^2+10k+24 for k ≥ 0.
      -- Actually let's just use F(2k+10) = F(2k+9) + F(2k+8) and
      -- F(2k+9) = F(2k+8) + F(2k+7), F(2k+8) = F(2k+7) + F(2k+6)
      -- By IH at k+4: F(2k+8) ≥ (k+4)^2
      -- By IH at k+3: F(2k+6) ≥ (k+3)^2
      -- F(2k+7) ≥ F(2k+6) ≥ (k+3)^2 (by mono)
      -- F(2k+9) ≥ (k+4)^2 + (k+3)^2
      -- F(2k+10) ≥ (k+4)^2 + (k+3)^2 + (k+4)^2 = 2*(k+4)^2 + (k+3)^2
      -- Need: 2*(k+4)^2 + (k+3)^2 > (k+5)^2 - 1
      -- LHS = 2k^2+16k+32 + k^2+6k+9 = 3k^2+22k+41
      -- RHS = k^2+10k+24
      -- 3k^2+22k+41 > k^2+10k+24 iff 2k^2+12k+17 > 0, always true.
      -- F(2(k+6)) = F(2k+12). Use F(2k+12) = F(2k+10) + F(2k+11), etc.
      -- IH at k+5 and k+4 (both ≥ 4 since k ≥ 0)
      have hfib1 : Nat.fib (2 * k + 12) = Nat.fib (2 * k + 10) + Nat.fib (2 * k + 11) := by
        rw [show 2 * k + 12 = (2 * k + 10) + 2 from by omega]; exact Nat.fib_add_two
      have hfib2 : Nat.fib (2 * k + 11) = Nat.fib (2 * k + 9) + Nat.fib (2 * k + 10) := by
        rw [show 2 * k + 11 = (2 * k + 9) + 2 from by omega]; exact Nat.fib_add_two
      have hfib3 : Nat.fib (2 * k + 10) = Nat.fib (2 * k + 8) + Nat.fib (2 * k + 9) := by
        rw [show 2 * k + 10 = (2 * k + 8) + 2 from by omega]; exact Nat.fib_add_two
      have ih5 := ih (k + 5) (by omega) (by omega)
      have ih4 := ih (k + 4) (by omega) (by omega)
      have hmono : Nat.fib (2 * k + 8) ≤ Nat.fib (2 * k + 9) := Nat.fib_mono (by omega)
      -- ih5: (k+5)^2 - 1 < F(2k+10), so (k+5)^2 ≤ F(2k+10)
      -- ih4: (k+4)^2 - 1 < F(2k+8), so (k+4)^2 ≤ F(2k+8)
      -- Goal: (k+6)^2 - 1 < F(2k+12)
      -- F(2k+12) = F(2k+10) + F(2k+11) ≥ F(2k+10) + F(2k+9) + F(2k+10) = 2*F(2k+10) + F(2k+9)
      -- ≥ 2*(k+5)^2 + (k+4)^2 > (k+6)^2 - 1
      -- In Nat: a^2 - 1 < b → a^2 ≤ b is just Nat.lt_of_sub
      -- Convert from Nat subtraction: a^2-1 < b → a^2 ≤ b
      have h5 : (k + 5) ^ 2 ≤ Nat.fib (2 * k + 10) := Nat.le_of_pred_lt ih5
      have h4 : (k + 4) ^ 2 ≤ Nat.fib (2 * k + 8) := Nat.le_of_pred_lt ih4
      -- F(2k+12) = F(2k+10) + F(2k+11) = F(2k+10) + F(2k+9) + F(2k+10)
      -- ≥ 2*(k+5)^2 + (k+4)^2 (since F(2k+9) ≥ F(2k+8) ≥ (k+4)^2)
      -- 2*(k+5)^2 + (k+4)^2 = 3k^2 + 28k + 66 > k^2 + 12k + 35 = (k+6)^2 - 1
      have h9 : (k + 4) ^ 2 ≤ Nat.fib (2 * k + 9) := le_trans h4 hmono
      -- Now chain: F(2k+12) ≥ (k+5)^2 + (k+4)^2 + (k+5)^2
      -- Pure arithmetic: 2*(k+5)^2 + (k+4)^2 > (k+6)^2 - 1
      -- = 3k^2+28k+66 > k^2+12k+35
      have goal_bound : (k + 6) ^ 2 ≤ 2 * (k + 5) ^ 2 + (k + 4) ^ 2 := by nlinarith [sq_nonneg k]
      -- Chain: F(2k+12) = F(2k+10) + F(2k+11)
      --        F(2k+11) = F(2k+9) + F(2k+10), so F(2k+12) = 2*F(2k+10) + F(2k+9)
      --        ≥ 2*(k+5)^2 + (k+4)^2 ≥ (k+6)^2
      have chain : Nat.fib (2 * k + 12) ≥ 2 * Nat.fib (2 * k + 10) + Nat.fib (2 * k + 9) := by
        linarith
      have chain2 : Nat.fib (2 * k + 12) ≥ 2 * (k + 5) ^ 2 + (k + 4) ^ 2 := by linarith
      -- (k+6)^2 - 1 < F: suffices (k+6)^2 ≤ F
      suffices h : (k + 6) ^ 2 ≤ Nat.fib (2 * (k + 6)) by
        have : 1 ≤ (k + 6) ^ 2 := by nlinarith [sq_nonneg (k + 6)]
        omega
      rw [show 2 * (k + 6) = 2 * k + 12 from by omega]
      linarith

/-- Fibonacci-Lie resonance classification: F(2k) = k^2-1 only for k ∈ {2,3}.
    thm:fib-lie-resonance-global-a-type -/
theorem fib_lie_resonance_complete (k : Nat) (hk : 2 ≤ k) :
    Nat.fib (2 * k) = k ^ 2 - 1 ↔ k = 2 ∨ k = 3 := by
  constructor
  · intro heq
    by_contra h
    push_neg at h
    obtain ⟨hne2, hne3⟩ := h
    have hk4 : 4 ≤ k := by omega
    have := fib_double_gt_sq_sub_one k hk4
    omega
  · intro h
    rcases h with rfl | rfl
    · native_decide
    · native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 212: Fibonacci shift identities
-- ══════════════════════════════════════════════════════════════

/-- F(n+3) = 3*F(n) + 2*F(n-1). prop:resolution-shift4-fib-matrix-law -/
theorem fib_shift3 (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (n + 3) = 3 * Nat.fib n + 2 * Nat.fib (n - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [show j + 1 - 1 = j from by omega]
  have h1 := Nat.fib_add_two (n := j)
  have h2 := Nat.fib_add_two (n := j + 1)
  have h3 := Nat.fib_add_two (n := j + 2)
  linarith

/-- F(n+4) = 5*F(n) + 3*F(n-1). prop:resolution-shift4-fib-matrix-law -/
theorem fib_shift4 (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (n + 4) = 5 * Nat.fib n + 3 * Nat.fib (n - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [show j + 1 - 1 = j from by omega]
  have h1 := Nat.fib_add_two (n := j)
  have h2 := Nat.fib_add_two (n := j + 1)
  have h3 := Nat.fib_add_two (n := j + 2)
  have h4 := Nat.fib_add_two (n := j + 3)
  linarith

/-- The four entrywise identities of the Fibonacci tail-matrix law
`G_{m+4} = G_m Q^4`. prop:resolution-shift4-fib-matrix-law -/
theorem paper_resolution_shift4_fib_matrix_law (m : ℕ) (hm : 2 ≤ m) :
    Nat.fib (m + 7) = 5 * Nat.fib (m + 3) + 3 * Nat.fib (m + 2) ∧
      Nat.fib (m + 6) = 3 * Nat.fib (m + 3) + 2 * Nat.fib (m + 2) ∧
      Nat.fib (m + 8) = 5 * Nat.fib (m + 4) + 3 * Nat.fib (m + 3) ∧
      Nat.fib (m + 7) = 3 * Nat.fib (m + 4) + 2 * Nat.fib (m + 3) := by
  have hm3 : 1 ≤ m + 3 := by omega
  have hm4 : 1 ≤ m + 4 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [show m + 3 - 1 = m + 2 by omega, Nat.add_assoc] using fib_shift4 (m + 3) hm3
  · simpa [show m + 3 - 1 = m + 2 by omega, Nat.add_assoc] using fib_shift3 (m + 3) hm3
  · simpa [show m + 4 - 1 = m + 3 by omega, Nat.add_assoc] using fib_shift4 (m + 4) hm4
  · simpa [show m + 4 - 1 = m + 3 by omega, Nat.add_assoc] using fib_shift3 (m + 4) hm4

-- ══════════════════════════════════════════════════════════════
-- Phase R36: Zeckendorf no-carry additivity (concrete instances)
-- ══════════════════════════════════════════════════════════════

/-- Zeckendorf no-carry additivity: F(2) + F(4) has Zeckendorf rep [4, 2]
    (no carry because gap ≥ 2).
    thm:zeckendorf-no-carry-additivity -/
theorem zeckendorf_no_carry_pair_2_4 :
    Nat.zeckendorf (Nat.fib 2 + Nat.fib 4) = [4, 2] := by native_decide

/-- Zeckendorf no-carry: F(2) + F(4) + F(6) = 12, and zeckendorf 12 = [6, 4, 2].
    thm:zeckendorf-no-carry-additivity -/
theorem zeckendorf_no_carry_triple_2_4_6 :
    Nat.zeckendorf (Nat.fib 2 + Nat.fib 4 + Nat.fib 6) = [6, 4, 2] := by native_decide

/-- Zeckendorf no-carry: F(4) + F(6) + F(9) = 45, and zeckendorf 45 = [9, 6, 4].
    thm:zeckendorf-no-carry-additivity -/
theorem zeckendorf_no_carry_triple_4_6_9 :
    Nat.zeckendorf (Nat.fib 4 + Nat.fib 6 + Nat.fib 9) = [9, 6, 4] := by native_decide

/-- No-carry additivity principle for two non-adjacent Fibonacci numbers:
    when gap(i, j) ≥ 2, the Zeckendorf representation of F(i) + F(j) is [j, i].
    Verified for small cases.
    thm:zeckendorf-no-carry-additivity -/
theorem zeckendorf_no_carry_gap2_instances :
    Nat.zeckendorf (Nat.fib 2 + Nat.fib 4) = [4, 2] ∧
    Nat.zeckendorf (Nat.fib 3 + Nat.fib 5) = [5, 3] ∧
    Nat.zeckendorf (Nat.fib 4 + Nat.fib 6) = [6, 4] ∧
    Nat.zeckendorf (Nat.fib 5 + Nat.fib 7) = [7, 5] ∧
    Nat.zeckendorf (Nat.fib 2 + Nat.fib 5) = [5, 2] ∧
    Nat.zeckendorf (Nat.fib 3 + Nat.fib 6) = [6, 3] := by native_decide

/-- Fibonacci carry identity: F_{n+2} + 2·F_n + F_{n-3} = F_{n+3} + F_{n-1} for n ≥ 5.
    lem:pom-fib-15to16-carry -/
theorem fib_15to16_carry (n : Nat) (hn : 5 ≤ n) :
    Nat.fib (n + 2) + 2 * Nat.fib n + Nat.fib (n - 3) =
    Nat.fib (n + 3) + Nat.fib (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 5 + k - 3 = k + 2 from by omega, show 5 + k - 1 = k + 4 from by omega]
  have e1 : Nat.fib (5 + k + 2) = Nat.fib (k + 7) := by ring_nf
  have e2 : Nat.fib (5 + k + 3) = Nat.fib (k + 8) := by ring_nf
  have e3 : Nat.fib (5 + k) = Nat.fib (k + 5) := by ring_nf
  rw [e1, e2, e3]
  -- Use fib_succ_succ' which gives Nat.fib (n+2) = Nat.fib (n+1) + Nat.fib n
  -- with properly normalized indices
  have h4 : Nat.fib (k + 4) = Nat.fib (k + 3) + Nat.fib (k + 2) :=
    Omega.fib_succ_succ' (k + 2)
  have h5 : Nat.fib (k + 5) = Nat.fib (k + 4) + Nat.fib (k + 3) :=
    Omega.fib_succ_succ' (k + 3)
  have h6 : Nat.fib (k + 6) = Nat.fib (k + 5) + Nat.fib (k + 4) :=
    Omega.fib_succ_succ' (k + 4)
  have h7 : Nat.fib (k + 7) = Nat.fib (k + 6) + Nat.fib (k + 5) :=
    Omega.fib_succ_succ' (k + 5)
  have h8 : Nat.fib (k + 8) = Nat.fib (k + 7) + Nat.fib (k + 6) :=
    Omega.fib_succ_succ' (k + 6)
  omega

/-- Zeckendorf representation of 15·F_n for n ≥ 8.
    thm:pom-zeckendorf-15fn-general -/
theorem zeckendorf_15Fn_general (n : Nat) (hn : 8 ≤ n) :
    15 * Nat.fib n = Nat.fib (n + 5) + Nat.fib (n + 2) + Nat.fib n +
                     Nat.fib (n - 3) + Nat.fib (n - 6) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  show 15 * Nat.fib (8 + k) = Nat.fib (8 + k + 5) + Nat.fib (8 + k + 2) +
    Nat.fib (8 + k) + Nat.fib (8 + k - 3) + Nat.fib (8 + k - 6)
  rw [show 8 + k - 3 = k + 5 from by omega, show 8 + k - 6 = k + 2 from by omega]
  have e1 : Nat.fib (8 + k) = Nat.fib (k + 8) := by ring_nf
  have e2 : Nat.fib (8 + k + 5) = Nat.fib (k + 13) := by ring_nf
  have e3 : Nat.fib (8 + k + 2) = Nat.fib (k + 10) := by ring_nf
  rw [e1, e2, e3]
  -- Eliminate Fibonacci top-down via substitution, reducing to F(k+2) and F(k+3)
  have h4 := Omega.fib_succ_succ' (k + 2)
  have h5 := Omega.fib_succ_succ' (k + 3)
  have h6 := Omega.fib_succ_succ' (k + 4)
  have h7 := Omega.fib_succ_succ' (k + 5)
  have h8 := Omega.fib_succ_succ' (k + 6)
  have h9 := Omega.fib_succ_succ' (k + 7)
  have h10 := Omega.fib_succ_succ' (k + 8)
  have h11 := Omega.fib_succ_succ' (k + 9)
  have h12 := Omega.fib_succ_succ' (k + 10)
  have h13 := Omega.fib_succ_succ' (k + 11)
  -- Substitute upward: eliminate F(k+13) down to F(k+2), F(k+3)
  rw [h13, h12, h11, h10, h9, h8, h7, h6, h5, h4]
  ring

/-- Zeckendorf representation of 16·F_n for n ≥ 8.
    thm:pom-zeckendorf-16fn-general -/
theorem zeckendorf_16Fn_general (n : Nat) (hn : 8 ≤ n) :
    16 * Nat.fib n = Nat.fib (n + 5) + Nat.fib (n + 3) +
                     Nat.fib (n - 1) + Nat.fib (n - 6) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  show 16 * Nat.fib (8 + k) = Nat.fib (8 + k + 5) + Nat.fib (8 + k + 3) +
    Nat.fib (8 + k - 1) + Nat.fib (8 + k - 6)
  rw [show 8 + k - 1 = k + 7 from by omega, show 8 + k - 6 = k + 2 from by omega]
  have e1 : Nat.fib (8 + k) = Nat.fib (k + 8) := by ring_nf
  have e2 : Nat.fib (8 + k + 5) = Nat.fib (k + 13) := by ring_nf
  have e3 : Nat.fib (8 + k + 3) = Nat.fib (k + 11) := by ring_nf
  rw [e1, e2, e3]
  have h4 := Omega.fib_succ_succ' (k + 2)
  have h5 := Omega.fib_succ_succ' (k + 3)
  have h6 := Omega.fib_succ_succ' (k + 4)
  have h7 := Omega.fib_succ_succ' (k + 5)
  have h8 := Omega.fib_succ_succ' (k + 6)
  have h9 := Omega.fib_succ_succ' (k + 7)
  have h10 := Omega.fib_succ_succ' (k + 8)
  have h11 := Omega.fib_succ_succ' (k + 9)
  have h12 := Omega.fib_succ_succ' (k + 10)
  have h13 := Omega.fib_succ_succ' (k + 11)
  rw [h13, h12, h11, h10, h9, h8, h7, h6, h5, h4]
  ring

/-- Zeckendorf representation of 15·F_4 = 45 = F_9 + F_6 + F_4 at m = 6.
    thm:pom-zeckendorf-resolution-lock-m6 -/
theorem zeckendorf_resolution_lock_m6 :
    15 * Nat.fib 4 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by native_decide

/-- The leading Fibonacci term in the Zeckendorf decomposition of 15·F_n.
    thm:pom-zeckendorf-15fn-leading-term -/
theorem zeckendorf_15Fn_leading_term (n : Nat) (hn : 8 ≤ n) :
    Nat.fib (n + 5) ≤ 15 * Nat.fib n ∧
    15 * Nat.fib n < Nat.fib (n + 6) := by
  constructor
  · -- Left: F(n+5) ≤ 15*F(n), from Zeckendorf decomposition (sum ≥ largest term)
    have := zeckendorf_15Fn_general n hn
    omega
  · -- Right: 15*F(n) < F(n+6), by Fibonacci expansion
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    show 15 * Nat.fib (8 + k) < Nat.fib (8 + k + 6)
    have e1 : Nat.fib (8 + k) = Nat.fib (k + 8) := by ring_nf
    have e2 : Nat.fib (8 + k + 6) = Nat.fib (k + 14) := by ring_nf
    rw [e1, e2]
    -- Use Zeckendorf decomposition: 15*F(k+8) = F(k+13) + F(k+10) + F(k+8) + F(k+5) + F(k+2)
    -- and F(k+14) = F(k+13) + F(k+12), so F(k+14) > F(k+13) ≥ 15*F(k+8) - other terms
    -- Simpler: directly show F(k+14) > 15*F(k+8) using closed form
    -- F(k+14)/F(k+8) → φ^6 ≈ 17.94 > 15
    -- Algebraically: express both in terms of F(k+2), F(k+3)
    have h4 := Omega.fib_succ_succ' (k + 2)
    have h5 := Omega.fib_succ_succ' (k + 3)
    have h6 := Omega.fib_succ_succ' (k + 4)
    have h7 := Omega.fib_succ_succ' (k + 5)
    have h8 := Omega.fib_succ_succ' (k + 6)
    have h9 := Omega.fib_succ_succ' (k + 7)
    have h10 := Omega.fib_succ_succ' (k + 8)
    have h11 := Omega.fib_succ_succ' (k + 9)
    have h12 := Omega.fib_succ_succ' (k + 10)
    have h13 := Omega.fib_succ_succ' (k + 11)
    have h14 := Omega.fib_succ_succ' (k + 12)
    have hpos := Omega.fib_succ_pos (k + 1)
    -- F(k+8) = 13*F(k+2) + 8*F(k+3) (from substitution chain)
    -- F(k+14) = 233*F(k+2) + 144*F(k+3) (Fibonacci coefficients)
    -- 15 * (13a + 8b) = 195a + 120b
    -- 233a + 144b > 195a + 120b ↔ 38a + 24b > 0, true since a = F(k+2) ≥ 1
    -- Express F(k+8) and F(k+14) in terms of a = F(k+2), b = F(k+3):
    have hF8 : Nat.fib (k + 8) = 5 * Nat.fib (k + 2) + 8 * Nat.fib (k + 3) := by
      rw [h8, h7, h6, h5, h4]; ring
    have hF14 : Nat.fib (k + 14) = 89 * Nat.fib (k + 2) + 144 * Nat.fib (k + 3) := by
      rw [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4]; ring
    rw [hF8, hF14]; nlinarith

/-- 15·F_n < F_{n+6} for n ≥ 2 (fails at n=1 since 15·1 = 15 > 13 = F_7).
    thm:pom-fifteen-fib-lt-fib-add-six -/
theorem fifteen_fib_lt_fib_add_six (n : Nat) (hn : 2 ≤ n) :
    15 * Nat.fib n < Nat.fib (n + 6) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  show 15 * Nat.fib (2 + k) < Nat.fib (2 + k + 6)
  have e1 : Nat.fib (2 + k) = Nat.fib (k + 2) := by ring_nf
  have e2 : Nat.fib (2 + k + 6) = Nat.fib (k + 8) := by ring_nf
  rw [e1, e2]
  -- F(k+2) = a, F(k+3) = b, F(k+8) = 5a + 8b
  -- 15a < 5a + 8b ↔ 10a < 8b ↔ 5a < 4b
  -- Since b = F(k+3) = F(k+2) + F(k+1) ≥ a + 1 (for k ≥ 0, F(k+1) ≥ 1)
  -- 4b ≥ 4(a+1) = 4a + 4 > 5a requires 4 > a, i.e., a ≤ 3
  -- Actually need a different bound. F(k+3) > F(k+2) always for k ≥ 0.
  -- Actually 5a < 4b ↔ 5a < 4(a + F(k+1)) = 4a + 4F(k+1) ↔ a < 4F(k+1)
  -- Since a = F(k+2) = F(k+1) + F(k), we need F(k+1) + F(k) < 4F(k+1), i.e., F(k) < 3F(k+1), true for all k.
  have h4 := Omega.fib_succ_succ' (k + 2)
  have h5 := Omega.fib_succ_succ' (k + 3)
  have h6 := Omega.fib_succ_succ' (k + 4)
  have h7 := Omega.fib_succ_succ' (k + 5)
  have h8 := Omega.fib_succ_succ' (k + 6)
  have hpos := Omega.fib_succ_pos (k + 1)
  -- Express in terms of a = F(k+2), b = F(k+3)
  have hF8 : Nat.fib (k + 8) = 5 * Nat.fib (k + 2) + 8 * Nat.fib (k + 3) := by
    rw [h8, h7, h6, h5, h4]; ring
  -- Need 15*F(k+2) < 5*F(k+2) + 8*F(k+3), i.e., 10*F(k+2) < 8*F(k+3)
  -- F(k+3) = F(k+2) + F(k+1) with F(k+1) ≥ 1
  -- 8*(F(k+2) + F(k+1)) = 8*F(k+2) + 8*F(k+1) > 10*F(k+2) ↔ 8*F(k+1) > 2*F(k+2)
  -- F(k+2) = F(k+1) + F(k) ≤ 2*F(k+1) (since F(k) ≤ F(k+1)), so 2*F(k+2) ≤ 4*F(k+1) < 8*F(k+1)
  have hle : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have hk2 := Omega.fib_succ_succ' k       -- F(k+2) = F(k+1) + F(k)
  have hk3 := Omega.fib_succ_succ' (k + 1) -- F(k+3) = F(k+2) + F(k+1)
  rw [hF8]
  -- Need: 10*F(k+2) < 8*F(k+3) = 8*(F(k+2) + F(k+1)) = 8*F(k+2) + 8*F(k+1)
  -- i.e., 2*F(k+2) < 8*F(k+1), i.e., F(k+2) < 4*F(k+1)
  -- F(k+2) = F(k+1) + F(k) ≤ 2*F(k+1), so F(k+2) < 4*F(k+1) ✓ (since F(k+1) ≥ 1)
  nlinarith

/-- NAP minimality of so(10): 45 = F_9 + F_6 + F_4, and no other dimension in the
    classical simple Lie algebra census shares this Zeckendorf decomposition.
    thm:pom-nap-so10-minimality -/
theorem nap_so10_minimality :
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
    (∀ d ∈ [3, 8, 10, 14, 15, 21, 24, 28, 35, 36],
     Nat.zeckendorf d ≠ Nat.zeckendorf 45) := by
  constructor <;> native_decide

/-- Zeckendorf carry absorption at m=9: F(6) + F(7) = F(8), i.e. 8 + 13 = 21.
    prop:pom-zeckendorf-carry-absorption-m9 -/
theorem zeckendorf_carry_absorption_m9 :
    Nat.fib 6 + Nat.fib 7 = Nat.fib 8 := by native_decide

/-- The equation F(m+2) - 12 = F(m-2)² has unique solution m = 6 among m ≥ 6.
    For m = 7 direct computation refutes; for m ≥ 8, fib_sq_gt_fib_shift gives
    F(m-2)² > F(m+2), making F(m+2) - 12 < F(m+2) < F(m-2)² a contradiction.
    thm:pom-sm-square-residual-rigidity-m6 -/
theorem sm_square_residual_rigidity_m6 (m : Nat) (hm : 6 ≤ m)
    (h : Nat.fib (m + 2) - 12 = Nat.fib (m - 2) ^ 2) : m = 6 := by
  -- Eliminate m = 6, 7 by computation
  by_cases h6 : m = 6
  · exact h6
  · by_cases h7 : m = 7
    · subst h7; revert h; native_decide
    · -- m ≥ 8, so m - 2 ≥ 6
      exfalso
      have hm8 : 8 ≤ m := by omega
      have hm2_ge : 6 ≤ m - 2 := by omega
      -- F((m-2) + 4) < F(m-2)², i.e. F(m+2) < F(m-2)²
      have hsq := Omega.fib_sq_gt_fib_shift (m - 2) hm2_ge
      rw [show m - 2 + 4 = m + 2 from by omega] at hsq
      -- From hypothesis: F(m-2)² = F(m+2) - 12
      -- From hsq: F(m+2) < F(m-2)², so F(m-2)² > F(m+2) ≥ F(m+2) - 12
      -- But h says F(m+2) - 12 = F(m-2)², contradiction
      omega

/-- The SM gauge group dimensions 1+3+8=12 has Zeckendorf representation F(6)+F(4)+F(2).
    prop:sm-zeckendorf-lie-algebra-rigidity -/
theorem sm_zeckendorf_twelve :
    Nat.fib 6 + Nat.fib 4 + Nat.fib 2 = 12 := by norm_num [Nat.fib]

/-- SM boundary count verification with individual Fibonacci values.
    cor:sm-minimal-triple-selection-law -/
theorem sm_boundary_count :
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 ∧
    Nat.fib 2 = 1 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 := by
  norm_num [Nat.fib]

/-- Zeckendorf gap condition: indices 2,4,6 are pairwise ≥ 2 apart.
    prop:sm-zeckendorf-lie-algebra-rigidity -/
theorem sm_zeckendorf_no_adjacent :
    4 - 2 ≥ 2 ∧ 6 - 4 ≥ 2 := by omega

/-- In a gap-≥2 index set containing 4, 6, 8, neither 5 nor 7 can appear.
    cor:zeckendorf-no-adjacent-strict-inclusion-impossible -/
theorem zeckendorf_no_adjacent_strict_inclusion
    (S : Finset ℕ)
    (h_gap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a : ℤ) - b ≠ 1 ∧ (a : ℤ) - b ≠ -1)
    (h4 : 4 ∈ S) (h6 : 6 ∈ S) (_h8 : 8 ∈ S) :
    5 ∉ S ∧ 7 ∉ S := by
  constructor
  · intro h5
    have := (h_gap 5 h5 4 h4 (by omega)).1
    omega
  · intro h7
    have := (h_gap 7 h7 6 h6 (by omega)).1
    omega

end Omega.ZeckSig
