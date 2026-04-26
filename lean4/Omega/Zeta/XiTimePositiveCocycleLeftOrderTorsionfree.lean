import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-positive-cocycle-left-order-torsionfree`. -/
theorem paper_xi_time_positive_cocycle_left_order_torsionfree {G : Type*} [Group G]
    (ell : G → ℤ) (hadd : ∀ g h : G, ell (g * h) = ell g + ell h)
    (hsep : ∀ g : G, g ≠ 1 → ell g ≠ 0) :
    (let P : Set G := {g | 0 < ell g};
      (∀ g h : G, g ∈ P → h ∈ P → g * h ∈ P) ∧
        (∀ g : G, g ∈ P → g⁻¹ ∉ P) ∧
          (∀ g : G, g ≠ 1 → g ∈ P ∨ g⁻¹ ∈ P) ∧
            (∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1)) := by
  dsimp
  have hell_one : ell (1 : G) = 0 := by
    have h := hadd (1 : G) (1 : G)
    simp only [mul_one] at h
    omega
  have hell_inv : ∀ g : G, ell g⁻¹ = -ell g := by
    intro g
    have h := hadd g g⁻¹
    have hsum : ell g + ell g⁻¹ = 0 := by
      simpa [hell_one] using h.symm
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g h hg hh
    rw [hadd]
    exact add_pos hg hh
  · intro g hg hginv
    rw [hell_inv] at hginv
    omega
  · intro g hg
    rcases lt_trichotomy (ell g) 0 with hneg | hzero | hpos
    · right
      rw [hell_inv]
      omega
    · exact False.elim (hsep g hg hzero)
    · exact Or.inl hpos
  · intro g n hn hpow_one
    by_contra hg
    have hell_pow : ∀ m : ℕ, ell (g ^ m) = (m : ℤ) * ell g := by
      intro m
      induction m with
      | zero =>
          simp [hell_one]
      | succ m ih =>
          calc
            ell (g ^ Nat.succ m) = ell (g ^ m * g) := by rw [pow_succ]
            _ = ell (g ^ m) + ell g := hadd (g ^ m) g
            _ = (m : ℤ) * ell g + ell g := by rw [ih]
            _ = ((m : ℤ) + 1) * ell g := by ring
            _ = (Nat.succ m : ℤ) * ell g := by simp [Nat.cast_succ]
    have hmul_zero : (n : ℤ) * ell g = 0 := by
      have h := congrArg ell hpow_one
      rw [hell_pow n] at h
      simpa [hell_one] using h
    have hn_ne : (n : ℤ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    rcases mul_eq_zero.mp hmul_zero with hn_zero | hell_zero
    · exact hn_ne hn_zero
    · exact hsep g hg hell_zero

end Omega.Zeta
