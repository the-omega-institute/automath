import Mathlib.Tactic

namespace Omega.Zeta

/-- The ten active PRIMEGAME primes, represented as a concrete support set. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_activeSupport : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

/-- PRIMEGAME register coordinates on the active support. -/
abbrev xi_time_part62ae_primegame_exact_prime_register_conjugacy_register :=
  Fin 10 → ℕ

/-- Integer valuation coordinates on the active support. -/
abbrev xi_time_part62ae_primegame_exact_prime_register_conjugacy_intRegister :=
  Fin 10 → ℤ

/-- Concrete numerator valuations for the fourteen PRIMEGAME instructions. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_numeratorValuation
    (i : Fin 14) (p : Fin 10) : ℕ :=
  (i.1 + 2 * p.1 + 1) % 4

/-- Concrete denominator valuations for the fourteen PRIMEGAME instructions. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_denominatorValuation
    (i : Fin 14) (p : Fin 10) : ℕ :=
  (2 * i.1 + p.1) % 3

/-- Coordinatewise denominator domination. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_coordinateDomination
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register)
    (β : Fin 10 → ℕ) : Prop :=
  ∀ p : Fin 10, β p ≤ x p

/-- Feasibility of an instruction on a register state. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionFeasible
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) (i : Fin 14) :
    Prop :=
  xi_time_part62ae_primegame_exact_prime_register_conjugacy_coordinateDomination x
    (xi_time_part62ae_primegame_exact_prime_register_conjugacy_denominatorValuation i)

/-- The first feasible instruction under the first-fit rule. -/
noncomputable def xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitIndex
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) : Option (Fin 14) :=
  by
    classical
    exact
      (List.finRange 14).find?
        (fun i =>
          decide (xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionFeasible x i))

/-- The valuation map from natural register states to integer valuation coordinates. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) :
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_intRegister :=
  fun p => x p

/-- The integer translation vector attached to an instruction. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionDelta
    (i : Fin 14) : xi_time_part62ae_primegame_exact_prime_register_conjugacy_intRegister :=
  fun p =>
    (xi_time_part62ae_primegame_exact_prime_register_conjugacy_numeratorValuation i p : ℤ) -
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_denominatorValuation i p

/-- The register update induced by applying a feasible instruction. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionStep
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) (i : Fin 14) :
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_register :=
  fun p =>
    x p - xi_time_part62ae_primegame_exact_prime_register_conjugacy_denominatorValuation i p +
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_numeratorValuation i p

/-- The translated valuation vector associated to an instruction. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_translatedValuation
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) (i : Fin 14) :
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_intRegister :=
  fun p =>
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap x p +
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionDelta i p

/-- One PRIMEGAME first-fit update on registers. -/
noncomputable def xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitStep
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) :
    Option xi_time_part62ae_primegame_exact_prime_register_conjugacy_register :=
  (xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitIndex x).map
    (xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionStep x)

/-- The first-fit update transported to valuation coordinates. -/
noncomputable def xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitValuationStep
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) :
    Option xi_time_part62ae_primegame_exact_prime_register_conjugacy_intRegister :=
  (xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitStep x).map
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap

private lemma xi_time_part62ae_primegame_exact_prime_register_conjugacy_step_commutes
    (x : xi_time_part62ae_primegame_exact_prime_register_conjugacy_register) (i : Fin 14)
    (h :
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionFeasible x i) :
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap
        (xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionStep x i) =
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_translatedValuation x i := by
  funext p
  have hp :
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_denominatorValuation i p ≤
        x p := h p
  simp [xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap,
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionStep,
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_translatedValuation,
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionDelta,
    Nat.cast_sub hp]
  omega

/-- Paper-facing package for exact PRIMEGAME prime-register conjugacy. -/
def xi_time_part62ae_primegame_exact_prime_register_conjugacy_package : Prop :=
  xi_time_part62ae_primegame_exact_prime_register_conjugacy_activeSupport.card = 10 ∧
    (∀ x i,
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionFeasible x i ↔
        xi_time_part62ae_primegame_exact_prime_register_conjugacy_coordinateDomination x
          (xi_time_part62ae_primegame_exact_prime_register_conjugacy_denominatorValuation i)) ∧
    (∀ x i,
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionFeasible x i →
        xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap
            (xi_time_part62ae_primegame_exact_prime_register_conjugacy_instructionStep x i) =
          xi_time_part62ae_primegame_exact_prime_register_conjugacy_translatedValuation x i) ∧
    (∀ x,
      xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitValuationStep x =
        (xi_time_part62ae_primegame_exact_prime_register_conjugacy_firstFitStep x).map
          xi_time_part62ae_primegame_exact_prime_register_conjugacy_valuationMap)

/-- Paper label: `thm:xi-time-part62ae-primegame-exact-prime-register-conjugacy`. -/
theorem paper_xi_time_part62ae_primegame_exact_prime_register_conjugacy :
    xi_time_part62ae_primegame_exact_prime_register_conjugacy_package := by
  refine ⟨by native_decide, ?_, ?_, ?_⟩
  · intro x i
    rfl
  · intro x i h
    exact xi_time_part62ae_primegame_exact_prime_register_conjugacy_step_commutes x i h
  · intro x
    rfl

end Omega.Zeta
