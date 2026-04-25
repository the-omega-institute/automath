import Mathlib.Tactic
import Omega.Conclusion.PrimeShiftPhaseVisibleTwoGenerator

namespace Omega.Conclusion

private theorem conclusion_prime_shift_phase_character_torus_cdim_factor_eq {A : Type*}
    [AddCommGroup A] {g : ℕ × ℕ → A} (hg : NatPairAdditive g) (u : ℕ × ℕ) :
    g u = primeShiftFactor (g (1, 0)) (g (0, 1)) u := by
  have hzero : g (0, 0) = 0 := by
    have h : g (0, 0) = g (0, 0) + g (0, 0) := by
      simpa using hg (0, 0) (0, 0)
    have h' := congrArg (fun x => x - g (0, 0)) h
    simpa using h'.symm
  rcases u with ⟨k, m⟩
  have hfirst : ∀ n : ℕ, g (n, 0) = n • g (1, 0)
  · intro n
    induction n with
    | zero =>
        simpa using hzero
    | succ n ih =>
        have h := hg (n, 0) (1, 0)
        simpa [ih, Nat.succ_eq_add_one, add_nsmul, one_nsmul, add_assoc, add_left_comm, add_comm]
          using h
  have hsecond : ∀ n : ℕ, g (0, n) = n • g (0, 1)
  · intro n
    induction n with
    | zero =>
        simpa using hzero
    | succ n ih =>
        have h := hg (0, n) (0, 1)
        simpa [ih, Nat.succ_eq_add_one, add_nsmul, one_nsmul, add_assoc, add_left_comm, add_comm]
          using h
  have hsplit := hg (k, 0) (0, m)
  simpa [primeShiftFactor, hfirst k, hsecond m, add_assoc, add_left_comm, add_comm] using hsplit

/-- Paper label: `cor:conclusion-prime-shift-phase-character-torus-cdim`. Any additive phase
character on the prime-shift ledger is determined by the two visible generators, hence by an
explicit `primeShiftFactor a ζ` on the visible quotient. -/
theorem paper_conclusion_prime_shift_phase_character_torus_cdim {A : Type*} [AddCommGroup A]
    (f : PrimeShiftLedger → A) (hzero : f (0, 0) = 0)
    (hmul : ∀ x y, f (primeShiftMul x y) = f x + f y) :
    ∃ a ζ : A, ∀ x : PrimeShiftLedger, f x = primeShiftFactor a ζ (primeShiftPi x) := by
  rcases paper_conclusion_prime_shift_phase_visible_two_generator f hzero hmul with ⟨g, hg, _⟩
  refine ⟨g (1, 0), g (0, 1), ?_⟩
  intro x
  rw [hg.2 x, conclusion_prime_shift_phase_character_torus_cdim_factor_eq hg.1 (primeShiftPi x)]

end Omega.Conclusion
