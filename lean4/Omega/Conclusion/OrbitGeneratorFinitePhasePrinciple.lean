import Omega.Conclusion.PrimeShiftPhaseVisibleTwoGenerator

namespace Omega.Conclusion

/-- Any additive map on the visible quotient `ℕ²` is determined by its values on the two basis
generators, hence factors through the two-parameter family `primeShiftFactor a ζ`. -/
private theorem orbitGenerator_factor_eq {A : Type*} [AddCommGroup A] {g : ℕ × ℕ → A}
    (hg : NatPairAdditive g) (u : ℕ × ℕ) :
    g u = primeShiftFactor (g (1, 0)) (g (0, 1)) u := by
  have hzero : g (0, 0) = 0 := by
    have h : g (0, 0) = g (0, 0) + g (0, 0) := by simpa using hg (0, 0) (0, 0)
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

/-- Orbit generation collapses every additive character of the prime-shift ledger to the two
visible invariants `(k, Ω(r))`, and therefore every such character is given by the explicit
two-parameter family `primeShiftFactor a ζ`.
    thm:conclusion-orbit-generator-finite-phase-principle -/
theorem paper_conclusion_orbit_generator_finite_phase_principle {A : Type*} [AddCommGroup A]
    (f : PrimeShiftLedger → A) (hzero : f (0, 0) = 0)
    (hmul : ∀ x y, f (primeShiftMul x y) = f x + f y) :
    (∃! g : ℕ × ℕ → A, NatPairAdditive g ∧ ∀ x : PrimeShiftLedger, f x = g (primeShiftPi x)) ∧
      ∃ a ζ : A, ∀ x : PrimeShiftLedger, f x = primeShiftFactor a ζ (primeShiftPi x) := by
  rcases paper_conclusion_prime_shift_phase_visible_two_generator f hzero hmul with
    ⟨g, hg, huniq⟩
  refine ⟨⟨g, hg, huniq⟩, ?_⟩
  rcases hg with ⟨hgAdd, hgFactor⟩
  refine ⟨g (1, 0), g (0, 1), ?_⟩
  intro x
  rw [hgFactor x, orbitGenerator_factor_eq hgAdd (primeShiftPi x)]

end Omega.Conclusion
