import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

lemma periodic_eq_add_mul {α : Type*} (f : ℕ → α) {p q r : ℕ}
    (hperiodic : ∀ n, f (n + p) = f n) :
    f (r + q * p) = f r := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hstep : f ((r + q * p) + p) = f (r + q * p) := hperiodic (r + q * p)
      calc
        f (r + Nat.succ q * p) = f ((r + q * p) + p) := by
          rw [Nat.succ_mul, Nat.add_assoc]
        _ = f (r + q * p) := hstep
        _ = f r := ih

/-- After aligning the mod-`2` and mod-`3` tails at `max N2 N3`, the paired residue sequence has
period `72 = lcm(8, 18)`. `thm:pom-resonance-mod6-period-q13-15` -/
theorem paper_pom_resonance_mod6_period_q13_15
    (u : ℕ → ZMod 2 × ZMod 3) (N2 N3 : ℕ)
    (h2 : ∀ n, (u (N2 + n + 8)).1 = (u (N2 + n)).1)
    (h3 : ∀ n, (u (N3 + n + 18)).2 = (u (N3 + n)).2) :
    ∀ n, u (max N2 N3 + n + 72) = u (max N2 N3 + n) := by
  have h2period : ∀ n, (u (N2 + n + 72)).1 = (u (N2 + n)).1 := by
    intro n
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      periodic_eq_add_mul (fun m => (u (N2 + m)).1)
        (p := 8) (q := 9) (r := n) (by
          intro m
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h2 m)
  have h3period : ∀ n, (u (N3 + n + 72)).2 = (u (N3 + n)).2 := by
    intro n
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      periodic_eq_add_mul (fun m => (u (N3 + m)).2)
        (p := 18) (q := 4) (r := n) (by
          intro m
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h3 m)
  intro n
  ext
  · have hleft : max N2 N3 + n + 72 = N2 + (max N2 N3 - N2 + n) + 72 := by
      omega
    have hright : max N2 N3 + n = N2 + (max N2 N3 - N2 + n) := by
      omega
    rw [hleft, hright]
    exact h2period (max N2 N3 - N2 + n)
  · have hleft : max N2 N3 + n + 72 = N3 + (max N2 N3 - N3 + n) + 72 := by
      omega
    have hright : max N2 N3 + n = N3 + (max N2 N3 - N3 + n) := by
      omega
    rw [hleft, hright]
    exact h3period (max N2 N3 - N3 + n)

end Omega.POM
