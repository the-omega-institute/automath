import Mathlib.Tactic
import Omega.Conclusion.PrimeShiftPhaseVisibleTwoGenerator

namespace Omega.Conclusion

open Omega.GroupUnification

private theorem conclusion_prime_shift_phase_indistinguishability_primeShiftOmega_shift
    (r : PrimeRegisterObject) : primeShiftOmega (primeRegisterShift r) = primeShiftOmega r := by
  let omegaHom : PrimeRegisterObject →+ ℕ :=
    { toFun := primeShiftOmega
      map_zero' := primeShiftOmega_zero
      map_add' := primeShiftOmega_add }
  have hcomp : AddMonoidHom.comp omegaHom primeRegisterShift = omegaHom := by
    apply Finsupp.addHom_ext
    intro t n
    simp [omegaHom, primeShiftOmega, primeBasis]
  exact congrArg (fun h : PrimeRegisterObject →+ ℕ => h r) hcomp

private theorem conclusion_prime_shift_phase_indistinguishability_primeShiftOmega_iterate_shift
    (n : ℕ) (r : PrimeRegisterObject) :
    primeShiftOmega ((primeRegisterShift^[n]) r) = primeShiftOmega r := by
  induction n generalizing r with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [conclusion_prime_shift_phase_indistinguishability_primeShiftOmega_shift]
      exact ih _

/-- Paper label: `prop:conclusion-prime-shift-phase-indistinguishability`. Two prime-shift ledger
states are indistinguishable by additive characters exactly when they have the same visible quotient
coordinates. -/
theorem paper_conclusion_prime_shift_phase_indistinguishability (x y : PrimeShiftLedger) :
    (∀ {A : Type*} [AddCommGroup A] (f : PrimeShiftLedger → A), f (0, 0) = 0 →
      (∀ u v, f (primeShiftMul u v) = f u + f v) → f x = f y) ↔ primeShiftPi x = primeShiftPi y := by
  rcases x with ⟨r, k⟩
  rcases y with ⟨s, l⟩
  simp only [primeShiftPi]
  constructor
  · intro hxy
    have hshiftCoord : k = l := by
      let f : PrimeShiftLedger → ULift ℤ := fun z => ⟨Int.ofNat z.2⟩
      have hcoord := hxy f (by simp [f]) (by
        intro u v
        rcases u with ⟨u, m⟩
        rcases v with ⟨v, n⟩
        apply ULift.ext
        simp [f, primeShiftMul])
      exact Int.ofNat.inj (congrArg ULift.down hcoord)
    have homegaCoord : primeShiftOmega r = primeShiftOmega s := by
      let f : PrimeShiftLedger → ULift ℤ := fun z => ⟨Int.ofNat (primeShiftOmega z.1)⟩
      have hcoord := hxy f (by simp [f]) (by
        intro u v
        rcases u with ⟨u, m⟩
        rcases v with ⟨v, n⟩
        apply ULift.ext
        change
          Int.ofNat (primeShiftOmega (u + (primeRegisterShift^[m]) v)) =
            Int.ofNat (primeShiftOmega u) + Int.ofNat (primeShiftOmega v)
        rw [primeShiftOmega_add,
          conclusion_prime_shift_phase_indistinguishability_primeShiftOmega_iterate_shift]
        norm_num)
      exact Int.ofNat.inj (congrArg ULift.down hcoord)
    exact Prod.ext hshiftCoord homegaCoord
  · intro hpi A _ f hzero hmul
    rcases paper_conclusion_prime_shift_phase_visible_two_generator f hzero hmul with
      ⟨g, hg, _⟩
    have hgpi : g (primeShiftPi (r, k)) = g (primeShiftPi (s, l)) := congrArg g hpi
    simpa [hg.2 (r, k), hg.2 (s, l)] using hgpi

end Omega.Conclusion
