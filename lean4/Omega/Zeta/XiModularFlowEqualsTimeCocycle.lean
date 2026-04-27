import Mathlib.Tactic

namespace Omega.Zeta

/-- The additive defect of an integer time length under composition. -/
def xi_modular_flow_equals_time_cocycle_time_cocycle {G : Type*} (comp : G → G → G)
    (ell : G → Int) (g h : G) : Int :=
  ell (comp g h) - ell g - ell h

/-- The integer boundary produced by changing gauge by a potential. -/
def xi_modular_flow_equals_time_cocycle_gauge_coboundary {G : Type*} (comp : G → G → G)
    (beta : G → Int) (g h : G) : Int :=
  beta (comp g h) - beta g - beta h

/-- Gauge-shifted length. -/
def xi_modular_flow_equals_time_cocycle_gauge_length {G : Type*} (ell beta : G → Int) :
    G → Int :=
  fun g => ell g + beta g

/-- Integer model for the modular phase multiplier exponent. -/
def xi_modular_flow_equals_time_cocycle_modular_phase (lambda : Int) (weight : Int) : Int :=
  lambda * weight

/-- Integer model for the modular flow exponent attached to one arrow. -/
def xi_modular_flow_equals_time_cocycle_modular_flow {G : Type*} (lambda : Int)
    (ell : G → Int) (g : G) : Int :=
  xi_modular_flow_equals_time_cocycle_modular_phase lambda (ell g)

/-- A concrete coboundary trivialization of an integer `1`-cocycle defect. -/
def xi_modular_flow_equals_time_cocycle_cohomology_trivial {G : Type*} (comp : G → G → G)
    (alpha : G → G → Int) : Prop :=
  ∃ beta : G → Int, ∀ g h, alpha g h =
    xi_modular_flow_equals_time_cocycle_gauge_coboundary comp beta g h

/-- Paper-facing statement for `thm:xi-modular-flow-equals-time-cocycle`. It records the
associative integer cocycle identity, the modular exponent formula, the gauge coboundary formula,
and the equivalence between cohomological triviality and an explicit gauge trivialization. -/
def xi_modular_flow_equals_time_cocycle_statement : Prop :=
  ∀ {G : Type*} (comp : G → G → G) (ell beta : G → Int) (lambda : Int)
    (_hassoc : ∀ g h k, comp (comp g h) k = comp g (comp h k)),
      (∀ g h k,
        xi_modular_flow_equals_time_cocycle_time_cocycle comp ell (comp g h) k +
            xi_modular_flow_equals_time_cocycle_time_cocycle comp ell g h =
          xi_modular_flow_equals_time_cocycle_time_cocycle comp ell g (comp h k) +
            xi_modular_flow_equals_time_cocycle_time_cocycle comp ell h k) ∧
      (∀ g h,
        xi_modular_flow_equals_time_cocycle_modular_flow lambda ell (comp g h) -
            xi_modular_flow_equals_time_cocycle_modular_flow lambda ell g -
              xi_modular_flow_equals_time_cocycle_modular_flow lambda ell h =
          xi_modular_flow_equals_time_cocycle_modular_phase lambda
            (xi_modular_flow_equals_time_cocycle_time_cocycle comp ell g h)) ∧
      (∀ g h,
        xi_modular_flow_equals_time_cocycle_time_cocycle comp
            (xi_modular_flow_equals_time_cocycle_gauge_length ell beta) g h =
          xi_modular_flow_equals_time_cocycle_time_cocycle comp ell g h +
            xi_modular_flow_equals_time_cocycle_gauge_coboundary comp beta g h) ∧
      (xi_modular_flow_equals_time_cocycle_cohomology_trivial comp
          (xi_modular_flow_equals_time_cocycle_time_cocycle comp ell) ↔
        ∃ gamma : G → Int, ∀ g h,
          xi_modular_flow_equals_time_cocycle_time_cocycle comp ell g h =
            xi_modular_flow_equals_time_cocycle_gauge_coboundary comp gamma g h)

/-- Paper label: `thm:xi-modular-flow-equals-time-cocycle`. -/
theorem paper_xi_modular_flow_equals_time_cocycle :
    xi_modular_flow_equals_time_cocycle_statement := by
  intro G comp ell beta lambda hassoc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g h k
    unfold xi_modular_flow_equals_time_cocycle_time_cocycle
    rw [hassoc g h k]
    ring
  · intro g h
    unfold xi_modular_flow_equals_time_cocycle_modular_flow
      xi_modular_flow_equals_time_cocycle_modular_phase
      xi_modular_flow_equals_time_cocycle_time_cocycle
    ring
  · intro g h
    unfold xi_modular_flow_equals_time_cocycle_time_cocycle
      xi_modular_flow_equals_time_cocycle_gauge_length
      xi_modular_flow_equals_time_cocycle_gauge_coboundary
    ring
  · unfold xi_modular_flow_equals_time_cocycle_cohomology_trivial
    rfl

end Omega.Zeta
