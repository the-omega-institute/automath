import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The rank-one fusion defect identity with Fibonacci seeds rigidly forces the Fibonacci
sequence. `thm:pom-rankone-fusion-defect-fibonacci-rigidity` -/
theorem paper_pom_rankone_fusion_defect_fibonacci_rigidity (G : Nat → ℝ) (hseed0 : G 0 = 0)
    (hseed1 : G 1 = 1) (hseed2 : G 2 = 1)
    (hdefect : ∀ a b : Nat, G (a + 2) * G (b + 2) = G (a + b + 2) + G a * G b)
    (hpos1 : 0 < G 3) (hpos2 : 0 < G 4) : ∀ n : Nat, G n = Nat.fib n := by
  have h4_formula : G 4 = G 3 ^ 2 - 1 := by
    have h := hdefect 1 1
    rw [hseed1] at h
    calc
      G 4 = G 3 * G 3 - 1 := by linarith
      _ = G 3 ^ 2 - 1 := by ring
  have h5_formula : G 5 = G 3 * G 4 - 1 := by
    have h := hdefect 2 1
    rw [hseed1, hseed2] at h
    linarith
  have h6_formula : G 6 = G 4 ^ 2 - 1 := by
    have h := hdefect 2 2
    rw [hseed2] at h
    calc
      G 6 = G 4 * G 4 - 1 := by linarith
      _ = G 4 ^ 2 - 1 := by ring
  have hcross := hdefect 3 1
  have h3_quad : G 3 ^ 2 = 2 * G 3 := by
    rw [h5_formula, h6_formula, h4_formula, hseed1] at hcross
    ring_nf at hcross ⊢
    nlinarith
  have h3_eq : G 3 = 2 := by
    nlinarith
  have h4_pos : 0 < G 4 := hpos2
  have h4_eq : G 4 = 3 := by
    rw [h4_formula, h3_eq] at h4_pos ⊢
    nlinarith
  have hslice1 : ∀ a : Nat, G (a + 3) = 2 * G (a + 2) - G a := by
    intro a
    have h := hdefect a 1
    rw [hseed1, h3_eq] at h
    linarith
  have hslice2 : ∀ a : Nat, G (a + 4) = 3 * G (a + 2) - G a := by
    intro a
    have h := hdefect a 2
    rw [hseed2, h4_eq] at h
    linarith
  have hrec : ∀ n : Nat, G (n + 2) = G (n + 1) + G n := by
    intro n
    have hA := hslice1 n
    have hB := hslice1 (n + 1)
    have hC := hslice2 n
    nlinarith
  have hpair : ∀ n : Nat, G n = Nat.fib n ∧ G (n + 1) = Nat.fib (n + 1) := by
    intro n
    induction n with
    | zero =>
        exact ⟨by simpa using hseed0, by simpa using hseed1⟩
    | succ n ih =>
        rcases ih with ⟨hn, hn1⟩
        refine ⟨hn1, ?_⟩
        calc
          G (n + 2) = G (n + 1) + G n := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec n
          _ = Nat.fib (n + 1) + Nat.fib n := by rw [hn1, hn]
          _ = Nat.fib (n + 2) := by
            have hfib : (Nat.fib (n + 2) : ℝ) = Nat.fib n + Nat.fib (n + 1) := by
              exact_mod_cast (Nat.fib_add_two (n := n))
            linarith
  intro n
  exact (hpair n).1

end Omega.POM
