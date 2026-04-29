import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

theorem paper_xi_time_part53da_equivariant_boundary_coding_order_six {A X : Type*}
    [AddCommGroup A] [Fintype X] (act : ZMod 6 → X → X) (x0 : X)
    (hfree : Function.Injective fun g : ZMod 6 => act g x0) (enc : X → A)
    (ρ : ZMod 6 →+ A) (hinj : Function.Injective enc)
    (hequiv : ∀ g x, enc (act g x) = ρ g + enc x) :
    ∃ a : A, (6 : ℕ) • a = 0 ∧ ∀ n : ℕ, n < 6 → n ≠ 0 → n • a ≠ 0 := by
  refine ⟨ρ 1, ?_, ?_⟩
  · have hzero : (6 : ℕ) • (1 : ZMod 6) = 0 := by
      change ((6 : ℕ) : ZMod 6) = 0
      exact (ZMod.natCast_eq_zero_iff 6 6).mpr dvd_rfl
    calc
      (6 : ℕ) • ρ 1 = ρ ((6 : ℕ) • (1 : ZMod 6)) := by
        exact (map_nsmul ρ 6 (1 : ZMod 6)).symm
      _ = 0 := by simp [hzero]
  · intro n hn hn0 hna
    have hact0 : act 0 x0 = x0 := by
      apply hinj
      simpa using hequiv 0 x0
    have hrho : ρ (n : ZMod 6) = 0 := by
      calc
        ρ (n : ZMod 6) = ρ (n • (1 : ZMod 6)) := by simp
        _ = n • ρ 1 := map_nsmul ρ n (1 : ZMod 6)
        _ = 0 := hna
    have hcollision : act (n : ZMod 6) x0 = act 0 x0 := by
      apply hinj
      calc
        enc (act (n : ZMod 6) x0) = ρ (n : ZMod 6) + enc x0 := hequiv (n : ZMod 6) x0
        _ = enc x0 := by simp [hrho]
        _ = enc (act 0 x0) := by simp [hact0]
    have hzmod : (n : ZMod 6) = 0 := hfree hcollision
    have hdiv : 6 ∣ n := (ZMod.natCast_eq_zero_iff n 6).mp hzmod
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn0) hn hdiv
