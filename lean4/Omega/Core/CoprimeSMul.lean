import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-! ### Coprime scalar annihilation

Bézout's identity in additive abelian groups: if two coprime integers both
annihilate an element, the element must be zero. -/

namespace Omega

/-- Coprime annihilators in an additive commutative group force zero:
    if q₁ • a = 0 and q₂ • a = 0 and gcd(q₁,q₂) = 1, then a = 0.
    Bézout identity applied in an abelian group.
    thm:pom-anom-coprime-two-point-test -/
theorem coprime_smul_eq_zero_of_both {G : Type*} [AddCommGroup G]
    (a : G) (q₁ q₂ : ℤ)
    (h1 : q₁ • a = 0) (h2 : q₂ • a = 0)
    (hcoprime : Int.gcd q₁ q₂ = 1) :
    a = 0 := by
  -- Obtain Bézout coefficients: ∃ u v, u * q₁ + v * q₂ = gcd q₁ q₂
  have hbez := Int.gcd_eq_gcd_ab q₁ q₂
  -- gcd q₁ q₂ = 1 (as Int)
  have hone : (Int.gcd q₁ q₂ : ℤ) = 1 := by exact_mod_cast hcoprime
  rw [hone] at hbez
  -- a = 1 • a = (u*q₁ + v*q₂) • a = u•(q₁•a) + v•(q₂•a) = 0
  have key : (1 : ℤ) • a = (0 : G) := by
    conv_lhs => rw [show (1 : ℤ) = q₁ * Int.gcdA q₁ q₂ + q₂ * Int.gcdB q₁ q₂ from hbez]
    rw [add_smul, mul_smul, mul_smul, smul_comm q₁, smul_comm q₂, h1, h2,
        smul_zero, smul_zero, add_zero]
  rwa [one_smul] at key

/-- In a torsion-free additive group, q • a = 0 iff a = 0 (for q ≠ 0).
    cor:pom-anom-one-point-zero-test -/
theorem torsion_free_smul_eq_zero_iff {G : Type*} [AddCommGroup G]
    [NoZeroSMulDivisors ℤ G]
    (a : G) (q : ℤ) (hq : q ≠ 0) :
    q • a = 0 ↔ a = 0 := by
  constructor
  · intro h; exact (smul_eq_zero.mp h).resolve_left hq
  · rintro rfl; exact smul_zero q

/-- Oracle collapse: "all moment orders >= 2 annihilate a" iff "some coprime pair does".
    thm:pom-anom-all-moments-collapse-to-two -/
theorem anom_oracle_collapse {G : Type*} [AddCommGroup G] (a : G) :
    (∀ q : ℤ, 2 ≤ q → q • a = 0) ↔
    (∃ q₁ q₂ : ℤ, 2 ≤ q₁ ∧ 2 ≤ q₂ ∧ Int.gcd q₁ q₂ = 1 ∧ q₁ • a = 0 ∧ q₂ • a = 0) := by
  constructor
  · intro h
    exact ⟨2, 3, le_refl 2, by omega, by native_decide, h 2 (le_refl 2), h 3 (by omega)⟩
  · rintro ⟨q₁, q₂, _, _, hcop, h1, h2⟩
    have ha : a = 0 := coprime_smul_eq_zero_of_both a q₁ q₂ h1 h2 hcop
    intro q _; rw [ha, smul_zero]

-- ══════════════════════════════════════════════════════════════
-- Phase 202: Torsion order divisibility
-- ══════════════════════════════════════════════════════════════

/-- q • a = 0 iff ord(a) | q, for element of finite order in an additive group.
    thm:pom-anom-torsion-eliminability-min-order -/
theorem smul_eq_zero_iff_order_dvd {G : Type*} [AddCommGroup G]
    (a : G) (n : ℕ) (hn : 0 < n)
    (hord : n • a = 0)
    (hmin : ∀ k : ℕ, 0 < k → k < n → k • a ≠ 0)
    (q : ℕ) :
    q • a = 0 ↔ n ∣ q := by
  constructor
  · intro hq
    -- Euclidean division: q = n * (q / n) + q % n
    have hrem := Nat.div_add_mod q n
    -- (q % n) • a = q • a - n * (q / n) • a = 0 - 0 = 0
    have hmod : (q % n) • a = 0 := by
      have h1 : (n * (q / n)) • a = 0 := by rw [mul_nsmul, hord, smul_zero]
      have h2 : q • a = (n * (q / n)) • a + (q % n) • a := by
        rw [← add_smul]; congr 1; omega
      rw [h1, zero_add] at h2; rw [← h2, hq]
    -- By minimality: q % n = 0, hence n | q
    by_contra h
    have hlt : q % n < n := Nat.mod_lt q hn
    have hpos : 0 < q % n := Nat.pos_of_ne_zero (fun h0 => h (Nat.dvd_of_mod_eq_zero h0))
    exact hmin (q % n) hpos hlt hmod
  · rintro ⟨k, rfl⟩
    rw [mul_nsmul, hord, smul_zero]

end Omega
